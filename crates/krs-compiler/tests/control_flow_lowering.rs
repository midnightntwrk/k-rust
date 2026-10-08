//! Hand-built IMP control-flow lowering and canonical source contract.

use std::collections::{BTreeMap, BTreeSet};

use krs_compiler::testing::assert_lowering_contract;
use krs_compiler::{
    EmittedK, LoweredDefinition, LoweringError, SourceMapNodeKind, lower_semantic_theory,
};
use krs_ir::testing;
use krs_ir::{
    ApplicationRef, CellAttribute, CellContentFrame, CellPost, ClaimModality, ConfigurationRoot,
    FixedCell, FixedCellClause, FixedCellPattern, FixedConfiguration, FixedConfigurationPattern,
    FixedConfigurationRewrite, FixedConfigurationVariable, FixedInitializerCell, FormatFragment,
    GroupAssociativity, GroupAssociativitySentence, ItemKind, ModuleId, NodeOrigin, PackageId,
    PrecedenceRelation, ProductionAttribute, ProductionFieldId, ProductionFieldReference,
    ProductionGroupId, ProductionResultSort, SemanticId, SentenceKind, StableItemId,
    StrictnessKind,
};
use krs_ir_levels::{
    DefinitionSentence, DefinitionTermKind, MapOperands, RuleBodyRef, SemanticClaim,
    SemanticContextAlias, SemanticModule, SemanticProduction, SemanticProductionItem, SemanticRule,
    SemanticRuleCondition, SemanticRuleLabel, SemanticScopedBinder, SemanticSimplification,
    SemanticSimplificationPriority, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm,
    SemanticTheory, SemanticValidationError, SemanticVariable,
};
use krs_test_support::kompile_reference;

const CALC_SYNTAX: &str = "KRS-CALC-GRAMMAR";
const CALC: &str = "KRS-CALC";
const IMP_SYNTAX: &str = "KRS-IMP-GRAMMAR";
const IMP: &str = "KRS-IMP";

fn package() -> PackageId {
    testing::package("KRS-IMP", "imp")
}

fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), module, name, kind)
}

fn origin(key: &str) -> NodeOrigin {
    testing::origin_in(key, package(), "src/imp.rs", testing::digest(), 0, 1)
}

fn sid(value: &str) -> SemanticId {
    SemanticId::new(value).unwrap()
}

fn field(value: &str) -> ProductionFieldId {
    ProductionFieldId::new(value).unwrap()
}

fn group(value: &str) -> ProductionGroupId {
    ProductionGroupId::new(value).unwrap()
}

fn sort(name: &str) -> SemanticSortRef {
    SemanticSortRef::Declared(item("calc_syntax", name, ItemKind::Sort))
}

fn variable(key: &str, name: &str, variable_sort: SemanticSortRef) -> SemanticTerm {
    SemanticTerm::variable(origin(key), variable_sort, sid(name))
}

fn application(key: &str, production: StableItemId, arguments: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::application(
        origin(key),
        sort("Stmt"),
        ApplicationRef::Declared(production),
        arguments,
    )
}

#[expect(
    clippy::too_many_lines,
    reason = "Builds the complete calculator grammar fixture in one place."
)]
fn calc_syntax_module() -> SemanticModule {
    let expr = sort("Expr");
    let stmt = sort("Stmt");
    let value = sort("Value");
    let kresult = sort("KResult");
    let assign = SemanticProduction::with_api(
        origin("calc.production.assign"),
        item("calc_syntax", "Assign", ItemKind::Constructor),
        stmt.clone(),
        vec![
            SemanticProductionItem::non_terminal(
                origin("calc.production.assign.name"),
                field("name"),
                SemanticSortRef::id(),
            ),
            SemanticProductionItem::terminal(origin("calc.production.assign.equals"), "=").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("calc.production.assign.expression"),
                field("expression"),
                expr.clone(),
            ),
            SemanticProductionItem::terminal(origin("calc.production.assign.semicolon"), ";")
                .unwrap(),
        ],
        vec![
            ProductionAttribute::Group {
                origin: origin("calc.production.assign.group"),
                group: group("stmt"),
            },
            ProductionAttribute::Strictness {
                origin: origin("calc.production.assign.strict"),
                kind: StrictnessKind::Strict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    origin("calc.production.assign.strict.field"),
                    field("expression"),
                )],
                result_sort: ProductionResultSort::new(
                    origin("calc.production.assign.strict.result"),
                    kresult.clone(),
                ),
            },
            ProductionAttribute::Format {
                origin: origin("calc.production.assign.format"),
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
        krs_ir::RustVisibility::Public,
        None,
    )
    .unwrap();
    let sequence = SemanticProduction::with_api(
        origin("calc.production.sequence"),
        item("calc_syntax", "Sequence", ItemKind::Constructor),
        stmt.clone(),
        vec![
            SemanticProductionItem::non_terminal(
                origin("calc.production.sequence.first"),
                field("first"),
                stmt.clone(),
            ),
            SemanticProductionItem::non_terminal(
                origin("calc.production.sequence.second"),
                field("second"),
                stmt.clone(),
            ),
        ],
        vec![
            ProductionAttribute::Group {
                origin: origin("calc.production.sequence.group"),
                group: group("seq-stmt"),
            },
            ProductionAttribute::Format {
                origin: origin("calc.production.sequence.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Newline,
                    FormatFragment::Item(2),
                ],
            },
        ],
        krs_ir::RustVisibility::Public,
        None,
    )
    .unwrap();
    SemanticModule::new(
        origin("calc.module.syntax"),
        ModuleId::new(CALC_SYNTAX).unwrap(),
        vec![],
        vec![
            SemanticSort::new(
                origin("calc.sort.expr"),
                item("calc_syntax", "Expr", ItemKind::Sort),
            ),
            SemanticSort::new(
                origin("calc.sort.kresult"),
                item("calc_syntax", "KResult", ItemKind::Sort),
            ),
            SemanticSort::new(
                origin("calc.sort.stmt"),
                item("calc_syntax", "Stmt", ItemKind::Sort),
            ),
            SemanticSort::new(
                origin("calc.sort.value"),
                item("calc_syntax", "Value", ItemKind::Sort),
            ),
        ],
        vec![
            SemanticSubsort::new(
                origin("calc.subsort.bool-value"),
                SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
                value.clone(),
            ),
            SemanticSubsort::new(
                origin("calc.subsort.id-expr"),
                SemanticSortRef::id(),
                expr.clone(),
            ),
            SemanticSubsort::new(origin("calc.subsort.value-expr"), value.clone(), expr),
            SemanticSubsort::new(origin("calc.subsort.value-kresult"), value, kresult),
        ],
        vec![assign, sequence],
        vec![
            PrecedenceRelation::new(
                origin("calc.precedence.stmt-sequence"),
                vec![group("stmt")],
                vec![group("seq-stmt")],
            )
            .unwrap(),
        ],
        vec![
            GroupAssociativitySentence::new(
                origin("calc.associativity.sequence"),
                GroupAssociativity::Right,
                vec![group("seq-stmt")],
            )
            .unwrap(),
        ],
        None,
        vec![],
    )
}

fn control_production(
    name: &str,
    items: Vec<SemanticProductionItem>,
    attributes: Vec<ProductionAttribute<SemanticSortRef, krs_ir::StableItemId>>,
) -> SemanticProduction {
    SemanticProduction::with_api(
        origin(&format!("imp.production.{name}")),
        item("imp_syntax", name, ItemKind::Constructor),
        sort("Stmt"),
        items,
        attributes,
        krs_ir::RustVisibility::Public,
        None,
    )
    .unwrap()
}

#[expect(
    clippy::too_many_lines,
    reason = "Builds the complete imperative grammar fixture in one place."
)]
fn imp_syntax_module() -> SemanticModule {
    let expr = sort("Expr");
    let stmt = sort("Stmt");
    let stmt_group = |key| ProductionAttribute::Group {
        origin: origin(key),
        group: group("stmt"),
    };
    let if_else = control_production(
        "IfThenElse",
        vec![
            SemanticProductionItem::terminal(origin("imp.if-else.if"), "if").unwrap(),
            SemanticProductionItem::terminal(origin("imp.if-else.open"), "(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.if-else.condition"),
                field("condition"),
                expr.clone(),
            ),
            SemanticProductionItem::terminal(origin("imp.if-else.close"), ")").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.if-else.then"),
                field("then_branch"),
                stmt.clone(),
            ),
            SemanticProductionItem::terminal(origin("imp.if-else.else"), "else").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.if-else.otherwise"),
                field("else_branch"),
                stmt.clone(),
            ),
        ],
        vec![
            stmt_group("imp.if-else.group"),
            ProductionAttribute::Strictness {
                origin: origin("imp.if-else.strict"),
                kind: StrictnessKind::Strict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    origin("imp.if-else.strict.field"),
                    field("condition"),
                )],
                result_sort: ProductionResultSort::new(
                    origin("imp.if-else.strict.result"),
                    sort("KResult"),
                ),
            },
            ProductionAttribute::Avoid {
                origin: origin("imp.if-else.avoid"),
            },
            ProductionAttribute::Format {
                origin: origin("imp.if-else.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(2),
                    FormatFragment::Item(3),
                    FormatFragment::Item(4),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(5),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(6),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(7),
                ],
            },
        ],
    );
    let if_then = control_production(
        "IfThen",
        vec![
            SemanticProductionItem::terminal(origin("imp.if.if"), "if").unwrap(),
            SemanticProductionItem::terminal(origin("imp.if.open"), "(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.if.condition"),
                field("condition"),
                expr.clone(),
            ),
            SemanticProductionItem::terminal(origin("imp.if.close"), ")").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.if.body"),
                field("body"),
                stmt.clone(),
            ),
        ],
        vec![
            stmt_group("imp.if.group"),
            ProductionAttribute::Format {
                origin: origin("imp.if.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(2),
                    FormatFragment::Item(3),
                    FormatFragment::Item(4),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(5),
                ],
            },
        ],
    );
    let while_loop = control_production(
        "While",
        vec![
            SemanticProductionItem::terminal(origin("imp.while.while"), "while").unwrap(),
            SemanticProductionItem::terminal(origin("imp.while.open"), "(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.while.condition"),
                field("condition"),
                expr,
            ),
            SemanticProductionItem::terminal(origin("imp.while.close"), ")").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("imp.while.body"),
                field("body"),
                stmt.clone(),
            ),
        ],
        vec![
            stmt_group("imp.while.group"),
            ProductionAttribute::Format {
                origin: origin("imp.while.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(2),
                    FormatFragment::Item(3),
                    FormatFragment::Item(4),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(5),
                ],
            },
        ],
    );
    let block = control_production(
        "Block",
        vec![
            SemanticProductionItem::terminal(origin("imp.block.open"), "{").unwrap(),
            SemanticProductionItem::non_terminal(origin("imp.block.body"), field("body"), stmt),
            SemanticProductionItem::terminal(origin("imp.block.close"), "}").unwrap(),
        ],
        vec![ProductionAttribute::Format {
            origin: origin("imp.block.format"),
            fragments: vec![
                FormatFragment::Item(1),
                FormatFragment::Indent,
                FormatFragment::Newline,
                FormatFragment::Item(2),
                FormatFragment::Dedent,
                FormatFragment::Newline,
                FormatFragment::Item(3),
            ],
        }],
    );
    let empty = control_production(
        "EmptyBlock",
        vec![
            SemanticProductionItem::terminal(origin("imp.empty.open"), "{").unwrap(),
            SemanticProductionItem::terminal(origin("imp.empty.close"), "}").unwrap(),
        ],
        vec![ProductionAttribute::Format {
            origin: origin("imp.empty.format"),
            fragments: vec![FormatFragment::Item(1), FormatFragment::Item(2)],
        }],
    );
    SemanticModule::new(
        origin("imp.module.syntax"),
        ModuleId::new(IMP_SYNTAX).unwrap(),
        vec![ModuleId::new(CALC_SYNTAX).unwrap()],
        vec![],
        vec![],
        vec![if_else, if_then, while_loop, block, empty],
        vec![],
        vec![],
        None,
        vec![],
    )
}

fn configuration_module() -> SemanticModule {
    let stmt = sort("Stmt");
    let k = sid("cell.k");
    let env = sid("cell.env");
    let configuration = FixedConfiguration::new(
        origin("calc.configuration"),
        sid("configuration.calc"),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                origin("calc.configuration.k"),
                k.clone(),
                "k",
                vec![CellAttribute::color(origin("calc.configuration.k.color"), "green").unwrap()],
                SemanticSortRef::k_sequence(),
            )
            .unwrap(),
            FixedCell::leaf(
                origin("calc.configuration.env"),
                env.clone(),
                "env",
                vec![
                    CellAttribute::color(origin("calc.configuration.env.color"), "yellow").unwrap(),
                ],
                SemanticSortRef::map(),
            )
            .unwrap(),
        ],
        origin("calc.configuration.initializer"),
        sid("initializer.calc"),
        vec![
            FixedConfigurationVariable::new(
                origin("calc.configuration.variable.pgm"),
                sid("PGM"),
                "PGM",
                stmt.clone(),
                true,
            )
            .unwrap(),
            FixedConfigurationVariable::new(
                origin("calc.configuration.variable.env"),
                sid("ENV"),
                "ENV",
                SemanticSortRef::map(),
                false,
            )
            .unwrap(),
        ],
        vec![
            FixedInitializerCell::term(
                origin("calc.configuration.initializer.k"),
                k,
                SemanticTerm::k_sequence(
                    origin("calc.configuration.initializer.k.sequence"),
                    stmt.clone(),
                    vec![variable("calc.configuration.initializer.pgm", "PGM", stmt)],
                ),
            ),
            FixedInitializerCell::term(
                origin("calc.configuration.initializer.env"),
                env,
                variable(
                    "calc.configuration.initializer.env.variable",
                    "ENV",
                    SemanticSortRef::map(),
                ),
            ),
        ],
    )
    .unwrap();
    SemanticModule::new(
        origin("calc.module"),
        ModuleId::new(CALC).unwrap(),
        vec![ModuleId::new(CALC_SYNTAX).unwrap()],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Some(configuration),
        vec![],
    )
}

fn bool_token(key: &str, value: &str) -> SemanticTerm {
    SemanticTerm::token(
        origin(key),
        SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
        value,
    )
    .unwrap()
}

fn k_rule(
    label: &str,
    item_name: &str,
    variables: Vec<SemanticVariable>,
    before: SemanticTerm,
    after: Vec<SemanticTerm>,
) -> SemanticRule {
    SemanticRule::new_configuration(
        origin(&format!("imp.rule.{label}")),
        item("imp", item_name, ItemKind::Rule),
        SentenceKind::Transition,
        variables,
        FixedConfigurationRewrite::new(
            origin(&format!("imp.rule.{label}.rewrite")),
            sid("configuration.calc"),
            vec![FixedCellClause::new(
                origin(&format!("imp.rule.{label}.k")),
                sid("cell.k"),
                SemanticTerm::k_sequence(
                    origin(&format!("imp.rule.{label}.before")),
                    sort("Stmt"),
                    vec![before],
                ),
                CellPost::Replace {
                    term: SemanticTerm::k_sequence(
                        origin(&format!("imp.rule.{label}.after")),
                        sort("Stmt"),
                        after,
                    ),
                },
                CellContentFrame::KSequenceTail {
                    origin: origin(&format!("imp.rule.{label}.frame")),
                    binding: None,
                },
            )],
            vec![sid("cell.env")],
        )
        .unwrap(),
    )
    .unwrap()
}

#[derive(Clone, Copy, Default)]
struct ControlOptions {
    invalid_first_label: bool,
    omit_if_true_wildcard: bool,
    adjuncts: bool,
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps related control-flow rule fixtures and their options together."
)]
fn control_rules(options: ControlOptions) -> Vec<SemanticRule> {
    let expr = sort("Expr");
    let stmt = sort("Stmt");
    let if_else = item("imp_syntax", "IfThenElse", ItemKind::Constructor);
    let if_then = item("imp_syntax", "IfThen", ItemKind::Constructor);
    let while_loop = item("imp_syntax", "While", ItemKind::Constructor);
    let block = item("imp_syntax", "Block", ItemKind::Constructor);
    let empty = item("imp_syntax", "EmptyBlock", ItemKind::Constructor);
    let sequence = item("calc_syntax", "Sequence", ItemKind::Constructor);
    let wildcard_then = "__krs_wildcard_if_false_then";
    let wildcard_else = "__krs_wildcard_if_true_else";

    let mut if_true_variables = vec![SemanticVariable::new(sid("S1"), stmt.clone())];
    if !options.omit_if_true_wildcard {
        if_true_variables.push(SemanticVariable::new(sid(wildcard_else), stmt.clone()));
    }
    let if_true = k_rule(
        "if-true",
        if options.invalid_first_label {
            "if.true"
        } else {
            "if-true"
        },
        if_true_variables,
        application(
            "imp.rule.if-true.subject",
            if_else.clone(),
            vec![
                bool_token("imp.rule.if-true.condition", "true"),
                variable("imp.rule.if-true.then", "S1", stmt.clone()),
                variable("imp.rule.if-true.else", wildcard_else, stmt.clone()),
            ],
        ),
        vec![variable("imp.rule.if-true.result", "S1", stmt.clone())],
    );
    let if_false = k_rule(
        "if-false",
        "if-false",
        vec![
            SemanticVariable::new(sid(wildcard_then), stmt.clone()),
            SemanticVariable::new(sid("S2"), stmt.clone()),
        ],
        application(
            "imp.rule.if-false.subject",
            if_else.clone(),
            vec![
                bool_token("imp.rule.if-false.condition", "false"),
                variable("imp.rule.if-false.then", wildcard_then, stmt.clone()),
                variable("imp.rule.if-false.else", "S2", stmt.clone()),
            ],
        ),
        vec![variable("imp.rule.if-false.result", "S2", stmt.clone())],
    );
    let normalize = k_rule(
        "if-else",
        "if-else",
        vec![
            SemanticVariable::new(sid("C"), expr.clone()),
            SemanticVariable::new(sid("S"), stmt.clone()),
        ],
        application(
            "imp.rule.if-else.subject",
            if_then,
            vec![
                variable("imp.rule.if-else.condition.before", "C", expr.clone()),
                variable("imp.rule.if-else.body.before", "S", stmt.clone()),
            ],
        ),
        vec![application(
            "imp.rule.if-else.result",
            if_else.clone(),
            vec![
                variable("imp.rule.if-else.condition.after", "C", expr.clone()),
                variable("imp.rule.if-else.body.after", "S", stmt.clone()),
                application("imp.rule.if-else.empty", empty.clone(), vec![]),
            ],
        )],
    );

    let repeated_while = application(
        "imp.rule.while.repeated",
        while_loop.clone(),
        vec![
            variable("imp.rule.while.condition.repeated", "C", expr.clone()),
            variable("imp.rule.while.body.repeated", "S", stmt.clone()),
        ],
    );
    let body_sequence = application(
        "imp.rule.while.sequence",
        sequence,
        vec![
            variable("imp.rule.while.body.sequence", "S", stmt.clone()),
            repeated_while,
        ],
    );
    let while_rule = k_rule(
        "while",
        "while",
        vec![
            SemanticVariable::new(sid("C"), expr.clone()),
            SemanticVariable::new(sid("S"), stmt.clone()),
        ],
        application(
            "imp.rule.while.subject",
            while_loop,
            vec![
                variable("imp.rule.while.condition.before", "C", expr.clone()),
                variable("imp.rule.while.body.before", "S", stmt.clone()),
            ],
        ),
        vec![application(
            "imp.rule.while.result",
            if_else,
            vec![
                variable("imp.rule.while.condition.after", "C", expr),
                application("imp.rule.while.block", block.clone(), vec![body_sequence]),
                application("imp.rule.while.empty", empty.clone(), vec![]),
            ],
        )],
    );
    let block_rule = k_rule(
        "block",
        "block",
        vec![SemanticVariable::new(sid("S"), stmt.clone())],
        application(
            "imp.rule.block.subject",
            block,
            vec![variable("imp.rule.block.body", "S", stmt.clone())],
        ),
        vec![
            variable("imp.rule.block.result", "S", stmt),
            application("imp.rule.block.empty", empty.clone(), vec![]),
        ],
    );
    let done = k_rule(
        "done",
        "done",
        vec![],
        application("imp.rule.done.subject", empty, vec![]),
        vec![],
    );
    vec![if_true, if_false, normalize, while_rule, block_rule, done]
}

fn context_alias() -> SemanticContextAlias {
    let here = sid("HERE");
    SemanticContextAlias::new(
        origin("imp.context.eval"),
        item("imp", "EvalContext", ItemKind::ContextAlias),
        origin("imp.context.eval.name"),
        "eval_context".into(),
        origin("imp.context.eval.here"),
        here.clone(),
        vec![SemanticVariable::new(here.clone(), sort("Stmt"))],
        FixedConfigurationPattern::new(
            origin("imp.context.eval.pattern"),
            sid("configuration.calc"),
            vec![FixedCellPattern::new(
                origin("imp.context.eval.k"),
                sid("cell.k"),
                SemanticTerm::k_sequence(
                    origin("imp.context.eval.sequence"),
                    sort("Stmt"),
                    vec![variable("imp.context.eval.here.term", "HERE", sort("Stmt"))],
                ),
                CellContentFrame::KSequenceTail {
                    origin: origin("imp.context.eval.frame"),
                    binding: None,
                },
            )],
            vec![sid("cell.env")],
        )
        .unwrap(),
    )
}

fn all_paths_claim() -> SemanticRule {
    let anonymous = sid("_B__krs_0");
    let existential = sid("n");
    let id_token =
        |key: &str| SemanticTerm::token(origin(key), SemanticSortRef::id(), "$n").unwrap();
    let map = |key: &str, value: SemanticTerm| {
        SemanticTerm::map(
            origin(key),
            MapOperands::entry(id_token(&format!("{key}.id")), value),
        )
    };
    SemanticRule::new_configuration(
        origin("imp.claim.branching"),
        item("imp", "Branching", ItemKind::Claim),
        SentenceKind::Claim,
        vec![
            SemanticVariable::new(
                anonymous.clone(),
                SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
            ),
            SemanticVariable::new(
                existential.clone(),
                SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
            ),
        ],
        FixedConfigurationRewrite::new(
            origin("imp.claim.branching.rewrite"),
            sid("configuration.calc"),
            vec![FixedCellClause::new(
                origin("imp.claim.branching.env"),
                sid("cell.env"),
                map(
                    "imp.claim.branching.before",
                    variable(
                        "imp.claim.branching.anonymous",
                        anonymous.as_str(),
                        SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
                    ),
                ),
                CellPost::Replace {
                    term: map(
                        "imp.claim.branching.after",
                        variable(
                            "imp.claim.branching.exists.rhs",
                            existential.as_str(),
                            SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
                        ),
                    ),
                },
                CellContentFrame::MapRemainder {
                    origin: origin("imp.claim.branching.frame"),
                    binding: None,
                },
            )],
            vec![sid("cell.k")],
        )
        .unwrap(),
    )
    .unwrap()
    .with_label(Some(
        SemanticRuleLabel::new(origin("imp.claim.branching.label"), "branching").unwrap(),
    ))
    .with_claim(Some(SemanticClaim::new(
        origin("imp.claim.branching.modality"),
        ClaimModality::AllPaths,
        Some(origin("imp.claim.branching.circularity")),
        vec![],
    )))
    .with_existentials(vec![SemanticScopedBinder::new(
        origin("imp.claim.branching.binder"),
        origin("imp.claim.branching.binder.name"),
        existential.clone(),
        origin("imp.claim.branching.binder.sort"),
        SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
    )])
    .with_ensures(Some(SemanticRuleCondition::new(
        origin("imp.claim.branching.ensures"),
        SemanticTerm::application(
            origin("imp.claim.branching.ensures.equals"),
            SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
            ApplicationRef::Builtin(krs_ir::BuiltinOperation::IntEqual),
            vec![
                variable(
                    "imp.claim.branching.exists.ensures",
                    existential.as_str(),
                    SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
                ),
                SemanticTerm::token(
                    origin("imp.claim.branching.five"),
                    SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
                    "5",
                )
                .unwrap(),
            ],
        ),
    )))
}

fn one_path_claim() -> SemanticRule {
    let empty_map = |key: &str| SemanticTerm::map(origin(key), MapOperands::Empty);
    SemanticRule::new_configuration(
        origin("imp.claim.one-path"),
        item("imp", "OnePath", ItemKind::Claim),
        SentenceKind::Claim,
        vec![],
        FixedConfigurationRewrite::new(
            origin("imp.claim.one-path.rewrite"),
            sid("configuration.calc"),
            vec![FixedCellClause::new(
                origin("imp.claim.one-path.env"),
                sid("cell.env"),
                empty_map("imp.claim.one-path.before"),
                CellPost::Replace {
                    term: empty_map("imp.claim.one-path.after"),
                },
                CellContentFrame::Exact,
            )],
            vec![sid("cell.k")],
        )
        .unwrap(),
    )
    .unwrap()
    .with_label(Some(
        SemanticRuleLabel::new(origin("imp.claim.one-path.label"), "one-path-claim").unwrap(),
    ))
    .with_claim(Some(SemanticClaim::new(
        origin("imp.claim.one-path.modality"),
        ClaimModality::OnePath,
        None,
        vec![],
    )))
}

fn simplification_rule() -> SemanticRule {
    let int_sort = SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int);
    let variable = sid("simplified");
    let body = SemanticTerm::rewrite(
        origin("imp.simplification.rewrite"),
        int_sort.clone(),
        SemanticTerm::application(
            origin("imp.simplification.add"),
            int_sort.clone(),
            ApplicationRef::Builtin(krs_ir::BuiltinOperation::IntAdd),
            vec![
                SemanticTerm::variable(
                    origin("imp.simplification.variable.left"),
                    int_sort.clone(),
                    variable.clone(),
                ),
                SemanticTerm::token(origin("imp.simplification.zero"), int_sort.clone(), "0")
                    .unwrap(),
            ],
        ),
        SemanticTerm::variable(
            origin("imp.simplification.variable.right"),
            int_sort.clone(),
            variable.clone(),
        ),
    )
    .unwrap();
    SemanticRule::new(
        origin("imp.simplification"),
        item("imp", "AddZero", ItemKind::Simplification),
        SentenceKind::Simplification,
        vec![SemanticVariable::new(variable, int_sort)],
        body,
    )
    .unwrap()
    .with_simplification(Some(SemanticSimplification::new(
        origin("imp.simplification.attribute"),
        Some(SemanticSimplificationPriority::new(
            origin("imp.simplification.priority"),
            42,
        )),
    )))
}

fn imp_module(options: ControlOptions) -> SemanticModule {
    let mut rules = control_rules(options);
    let context_aliases = if options.adjuncts {
        rules.extend([all_paths_claim(), one_path_claim(), simplification_rule()]);
        vec![context_alias()]
    } else {
        vec![]
    };
    SemanticModule::new_with_context_aliases(
        origin("imp.module"),
        ModuleId::new(IMP).unwrap(),
        vec![
            ModuleId::new(IMP_SYNTAX).unwrap(),
            ModuleId::new(CALC).unwrap(),
        ],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        None,
        context_aliases,
        rules,
    )
}

fn control_flow_theory(options: ControlOptions) -> Result<SemanticTheory, SemanticValidationError> {
    SemanticTheory::new(vec![
        imp_module(options),
        configuration_module(),
        imp_syntax_module(),
        calc_syntax_module(),
    ])
}

fn assert_exact_source(source: &str) {
    expect_test::expect![[r#"
        module KRS-CALC-SYNTAX
          imports KRS-CALC-GRAMMAR-SYNTAX
        endmodule

        module KRS-CALC
          imports KRS-CALC-GRAMMAR
          imports KRS-CALC-SYNTAX
          imports MAP

          configuration
            <k color="green"> $PGM:Stmt </k>
            <env color="yellow"> $ENV:Map </env>

        endmodule

        module KRS-CALC-GRAMMAR-SYNTAX
          imports BOOL-SYNTAX
          imports ID-SYNTAX

          syntax Expr
          syntax KResult
          syntax Stmt
          syntax Value

          syntax Stmt ::= Id "=" Expr ";" [symbol(assign), group(krsgroup-35f1322f2f4f01e6affff031), strict(2), result(KResult), format(%1 %2 %3%4)]
          syntax Stmt ::= Stmt Stmt [symbol(sequence), group(krsgroup-ef11204726b39d86ee1fe653), format(%1%n%2)]

          syntax Expr ::= Id
          syntax Expr ::= Value
          syntax Value ::= Bool
          syntax KResult ::= Value

          syntax priority krsgroup-35f1322f2f4f01e6affff031 > krsgroup-ef11204726b39d86ee1fe653

          syntax right krsgroup-ef11204726b39d86ee1fe653
        endmodule

        module KRS-CALC-GRAMMAR
          imports KRS-CALC-GRAMMAR-SYNTAX
        endmodule

        module KRS-IMP-SYNTAX
          imports KRS-CALC-SYNTAX
          imports KRS-IMP-GRAMMAR-SYNTAX
        endmodule

        module KRS-IMP
          imports BOOL-SYNTAX
          imports KRS-CALC
          imports KRS-IMP-GRAMMAR
          imports KRS-IMP-SYNTAX

          rule [block]:
            <k> { S:Stmt } => S:Stmt ~> { } ... </k>
          rule [done]:
            <k> { } => .K ... </k>
          rule [if-else]:
            <k> if ( C:Expr ) S:Stmt => if ( C:Expr ) S:Stmt else { } ... </k>
          rule [if-false]:
            <k> if ( false ) _ else S2:Stmt => S2:Stmt ... </k>
          rule [if-true]:
            <k> if ( true ) S1:Stmt else _ => S1:Stmt ... </k>
          rule [while]:
            <k> while ( C:Expr ) S:Stmt => if ( C:Expr ) { S:Stmt while ( C:Expr ) S:Stmt } else { } ... </k>
        endmodule

        module KRS-IMP-GRAMMAR-SYNTAX
          imports KRS-CALC-GRAMMAR-SYNTAX

          syntax Stmt ::= "{" Stmt "}" [symbol(block), format(%1%i%n%2%d%n%3)]
          syntax Stmt ::= "{" "}" [symbol(emptyBlock), format(%1%2)]
          syntax Stmt ::= "if" "(" Expr ")" Stmt [symbol(ifThen), group(krsgroup-35f1322f2f4f01e6affff031), format(%1 %2%3%4 %5)]
          syntax Stmt ::= "if" "(" Expr ")" Stmt "else" Stmt [symbol(ifThenElse), group(krsgroup-35f1322f2f4f01e6affff031), strict(1), result(KResult), avoid, format(%1 %2%3%4 %5 %6 %7)]
          syntax Stmt ::= "while" "(" Expr ")" Stmt [symbol(while), group(krsgroup-35f1322f2f4f01e6affff031), format(%1 %2%3%4 %5)]
        endmodule

        module KRS-IMP-GRAMMAR
          imports KRS-CALC-GRAMMAR
          imports KRS-IMP-GRAMMAR-SYNTAX
        endmodule
    "#]]
    .assert_eq(source);
}

fn assert_definition_structure(lowered: &LoweredDefinition) {
    let modules = lowered
        .definition()
        .modules()
        .iter()
        .map(|module| (module.id().as_str(), module))
        .collect::<BTreeMap<_, _>>();
    // The `pub` grammar is program syntax, so it lives in the grammar
    // package's `-SYNTAX` module.
    let syntax = modules[format!("{IMP_SYNTAX}-SYNTAX").as_str()];
    let productions = syntax
        .sentences()
        .iter()
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production) => Some(production),
            _ => None,
        })
        .map(|production| (production.symbol().emitted_name(), production))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        productions.keys().copied().collect::<Vec<_>>(),
        ["block", "emptyBlock", "ifThen", "ifThenElse", "while"]
    );
    let if_else = productions["ifThenElse"];
    assert!(if_else.attributes().iter().any(|attribute| matches!(
        attribute,
        ProductionAttribute::Strictness { fields, .. }
            if fields.iter().map(krs_ir::ProductionFieldReference::field).eq([&field("condition")])
    )));
    assert!(
        if_else
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, ProductionAttribute::Avoid { .. }))
    );
    assert!(
        !productions["while"]
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, ProductionAttribute::Strictness { .. }))
    );

    let rules = modules[IMP]
        .sentences()
        .iter()
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule) => Some(rule),
            _ => None,
        })
        .map(|rule| (rule.label().emitted_name(), rule))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        rules.keys().copied().collect::<Vec<_>>(),
        ["block", "done", "if-else", "if-false", "if-true", "while"]
    );
    assert!(rules.values().all(|rule| matches!(
        rule.relational_body(),
        RuleBodyRef::Configuration { body, .. }
            if body.clauses().len() == 1 && body.omitted_siblings().len() == 1
    )));
    let RuleBodyRef::Configuration { body: done, .. } = rules["done"].relational_body() else {
        unreachable!()
    };
    assert!(matches!(
        done.clauses()[0].after(),
        CellPost::Replace { term }
            if matches!(term.kind(), DefinitionTermKind::KSequence { items, .. }
                if items.is_empty())
    ));
    let RuleBodyRef::Configuration { body: block, .. } = rules["block"].relational_body() else {
        unreachable!()
    };
    assert!(matches!(
        block.clauses()[0].after(),
        CellPost::Replace { term }
            if matches!(term.kind(), DefinitionTermKind::KSequence { items, .. }
                if items.len() == 2)
    ));
}

fn assert_sidecars(emitted: &EmittedK) {
    let label_names = emitted
        .symbol_map()
        .entries()
        .iter()
        .filter_map(|entry| match entry.identity() {
            krs_compiler::MappedIdentity::Label(_) => Some(entry.emitted_name()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        label_names,
        BTreeSet::from(["block", "done", "if-else", "if-false", "if-true", "while"])
    );
    let mut counts = BTreeMap::new();
    let mut missing = BTreeMap::new();
    for entry in emitted.source_map().entries() {
        *counts.entry(entry.node_kind()).or_insert(0_usize) += 1;
        if entry.generated().is_none() {
            *missing.entry(entry.node_kind()).or_insert(0_usize) += 1;
        }
    }
    assert_eq!(counts[&SourceMapNodeKind::Production], 7);
    assert_eq!(counts[&SourceMapNodeKind::Rule], 6);
    assert_eq!(counts[&SourceMapNodeKind::ConfigurationRewrite], 6);
    assert_eq!(counts[&SourceMapNodeKind::CellClause], 6);
    assert_eq!(counts[&SourceMapNodeKind::CellFrame], 6);
    assert_eq!(missing[&SourceMapNodeKind::ProductionGroup], 2);
    assert_eq!(missing[&SourceMapNodeKind::ConfigurationRewrite], 6);
}

#[test]
fn exact_control_flow_lowers_and_emits_canonical_k() {
    let semantic = control_flow_theory(ControlOptions::default()).unwrap();
    let (lowered, emitted) = assert_lowering_contract(&semantic);
    assert_definition_structure(&lowered);
    assert_exact_source(emitted.source());
    assert_sidecars(&emitted);
}

#[test]
fn context_alias_and_claim_adjuncts_lower_emit_and_map_every_distinct_role() {
    let semantic = control_flow_theory(ControlOptions {
        adjuncts: true,
        ..ControlOptions::default()
    })
    .unwrap();
    let (lowered, emitted) = assert_lowering_contract(&semantic);
    let source = emitted.source();

    assert!(
        source.contains("context alias [evalContext]:\n    <k> HERE ... </k>"),
        "{source}"
    );
    assert!(source.contains("[simplification(42), label("), "{source}");
    assert!(!source.contains("\n    [simplification"), "{source}");
    assert!(!source.contains("claim"), "{source}");

    let main = lowered.definition().main_module().as_str();
    let spec = emitted
        .spec()
        .expect("claims are emitted as a specification");
    assert_eq!(spec.module(), format!("{main}-SPEC"));
    let spec = spec.source();
    assert!(
        spec.starts_with(&format!(
            "requires \"definition.k\"\n\nmodule {main}-SPEC\n  imports {main}\n\n  claim "
        )),
        "{spec}"
    );
    assert!(spec.ends_with("endmodule\n"), "{spec}");
    assert!(spec.contains("claim [branching]:"), "{spec}");
    assert!(spec.contains("_B:Bool"), "{spec}");
    assert!(spec.contains("?N:Int"), "{spec}");
    assert!(spec.contains("ensures "), "{spec}");
    assert!(spec.contains("[circularity]"), "{spec}");
    assert!(spec.contains("claim [one-path-claim]:"), "{spec}");
    assert!(spec.contains("[one-path]"), "{spec}");
    assert!(!spec.contains("all-path"), "{spec}");
    assert!(!spec.contains("rule "), "{spec}");

    for (kind, count, artifact) in [
        (SourceMapNodeKind::ContextAlias, 3, "definition.k"),
        (SourceMapNodeKind::ClaimModality, 2, "spec.k"),
        (SourceMapNodeKind::ClaimCircularity, 1, "spec.k"),
        (SourceMapNodeKind::ClaimBinder, 3, "spec.k"),
        (SourceMapNodeKind::ClaimEnsures, 1, "spec.k"),
        (SourceMapNodeKind::Simplification, 1, "definition.k"),
        (SourceMapNodeKind::SimplificationPriority, 1, "definition.k"),
    ] {
        let entries = emitted
            .source_map()
            .entries()
            .iter()
            .filter(|entry| entry.node_kind() == kind)
            .collect::<Vec<_>>();
        assert_eq!(entries.len(), count, "unexpected {kind:?} entry count");
        assert!(
            entries.iter().all(|entry| entry
                .generated()
                .is_some_and(|range| range.artifact() == artifact)),
            "at least one {kind:?} entry has no generated range in {artifact}"
        );
    }
}

#[test]
fn undeclared_wildcard_and_invalid_control_label_fail_typed() {
    assert!(matches!(
        control_flow_theory(ControlOptions {
            omit_if_true_wildcard: true,
            ..ControlOptions::default()
        }),
        Err(SemanticValidationError::DanglingVariable(_))
    ));
    let invalid = control_flow_theory(ControlOptions {
        invalid_first_label: true,
        ..ControlOptions::default()
    })
    .unwrap();
    assert!(matches!(
        lower_semantic_theory(&invalid),
        Err(LoweringError::InvalidEmittedName {
            role: "rule label",
            value,
        }) if value == "if.true"
    ));
}

#[test]
#[ignore = "requires pin-matched K 7.1.337 tools"]
fn emitted_control_flow_source_compiles_with_pinned_reference_frontend() {
    let (_, emitted) =
        assert_lowering_contract(&control_flow_theory(ControlOptions::default()).unwrap());
    let _temporary = kompile_reference(emitted.source(), IMP, IMP_SYNTAX)
        .enable_search()
        .run();
}
