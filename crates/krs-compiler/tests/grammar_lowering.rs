//! Structured grammar reaches Definition IR and canonical K source.

use krs_compiler::testing::assert_lowering_contract;
use krs_ir::testing;
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ConfigurationRoot, FixedCell,
    FixedConfiguration, FixedConfigurationVariable, FixedInitializerCell, FormatFragment,
    GroupAssociativity, GroupAssociativitySentence, HookOperation, ItemKind, ModuleId, NodeOrigin,
    PackageId, PrecedenceRelation, ProductionAttribute, ProductionFieldId,
    ProductionFieldReference, ProductionGroupId, ProductionResultSort, SemanticId, SentenceKind,
    StableItemId, StrictnessKind,
};
use krs_ir_levels::{
    SemanticModule, SemanticProduction, SemanticProductionItem, SemanticRule, SemanticSort,
    SemanticSortRef, SemanticSubsort, SemanticTerm, SemanticTheory, SemanticVariable,
};

fn package() -> PackageId {
    testing::package("KRS-GRAMMAR", "grammar")
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "expr", name, kind)
}

fn origin(key: &str) -> NodeOrigin {
    testing::origin_in(
        key,
        package(),
        "src/expr.rs",
        testing::digest_with("1".repeat(64)),
        0,
        1,
    )
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Checks the complete hook catalog with shared grammar fixtures."
)]
fn every_hook_emits_its_catalog_spelling() {
    let g1 = item("G1Point", ItemKind::Sort);
    let g2 = item("G2Point", ItemKind::Sort);
    let mut productions = Vec::new();
    for (name, sort, arity) in [("G1Point", g1.clone(), 2), ("G2Point", g2.clone(), 4)] {
        let items = (0..arity)
            .map(|field| {
                SemanticProductionItem::non_terminal(
                    origin(&format!("{name}.field.{field}")),
                    ProductionFieldId::new(format!("field{field}")).unwrap(),
                    SemanticSortRef::int(),
                )
            })
            .collect();
        productions.push(
            SemanticProduction::new(
                origin(&format!("{name}.production")),
                item(name, ItemKind::Constructor),
                SemanticSortRef::declared(sort),
                items,
                vec![],
            )
            .unwrap(),
        );
    }
    for (index, operation) in HookOperation::ALL.into_iter().enumerate() {
        let expected = match operation {
            HookOperation::KryptoKeccak256Raw => "KRYPTO.keccak256raw",
            HookOperation::KryptoSha256Raw => "KRYPTO.sha256raw",
            HookOperation::KryptoRipemd160Raw => "KRYPTO.ripemd160raw",
            HookOperation::KryptoEcdsaRecover => "KRYPTO.ecdsaRecover",
            HookOperation::KryptoBn128Valid => "KRYPTO.bn128valid",
            HookOperation::KryptoBn128Add => "KRYPTO.bn128add",
            HookOperation::KryptoBn128Mul => "KRYPTO.bn128mul",
            HookOperation::KryptoBn128G2Valid => "KRYPTO.bn128g2valid",
            HookOperation::KryptoBn128Ate => "KRYPTO.bn128ate",
        };
        let (result_sort, argument_sorts) =
            if let Some((result, arguments)) = operation.builtin_signature() {
                (
                    SemanticSortRef::Builtin(result),
                    arguments
                        .iter()
                        .copied()
                        .map(SemanticSortRef::Builtin)
                        .collect::<Vec<_>>(),
                )
            } else {
                match operation {
                    HookOperation::KryptoBn128Valid => (
                        SemanticSortRef::bool(),
                        vec![SemanticSortRef::declared(g1.clone())],
                    ),
                    HookOperation::KryptoBn128G2Valid => (
                        SemanticSortRef::bool(),
                        vec![SemanticSortRef::declared(g2.clone())],
                    ),
                    HookOperation::KryptoBn128Add => {
                        let point = SemanticSortRef::declared(g1.clone());
                        (point.clone(), vec![point.clone(), point])
                    }
                    HookOperation::KryptoBn128Mul => {
                        let point = SemanticSortRef::declared(g1.clone());
                        (point.clone(), vec![point, SemanticSortRef::int()])
                    }
                    HookOperation::KryptoKeccak256Raw
                    | HookOperation::KryptoSha256Raw
                    | HookOperation::KryptoRipemd160Raw
                    | HookOperation::KryptoEcdsaRecover
                    | HookOperation::KryptoBn128Ate => unreachable!(),
                }
            };
        let mut items = vec![
            SemanticProductionItem::terminal(
                origin(&format!("hook.{index}.terminal")),
                format!("Hook{index}("),
            )
            .unwrap(),
        ];
        items.extend(argument_sorts.into_iter().enumerate().map(|(field, sort)| {
            SemanticProductionItem::non_terminal(
                origin(&format!("hook.{index}.field.{field}")),
                ProductionFieldId::new(format!("field{field}")).unwrap(),
                sort,
            )
        }));
        productions.push(
            SemanticProduction::new(
                origin(&format!("hook.{index}.production")),
                item(&format!("Hook{index}"), ItemKind::Constructor),
                result_sort,
                items,
                vec![
                    ProductionAttribute::Function {
                        origin: origin(&format!("hook.{index}.function")),
                    },
                    ProductionAttribute::Total {
                        origin: origin(&format!("hook.{index}.total")),
                    },
                    ProductionAttribute::Hook {
                        origin: origin(&format!("hook.{index}.attribute")),
                        operation,
                    },
                ],
            )
            .unwrap(),
        );
        assert_eq!(operation.to_string(), expected);
    }
    let cell = SemanticId::new("cell.k").unwrap();
    let configuration = FixedConfiguration::new(
        origin("hooks.configuration"),
        SemanticId::new("configuration").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                origin("hooks.cell"),
                cell.clone(),
                "k",
                vec![],
                SemanticSortRef::int(),
            )
            .unwrap(),
        ],
        origin("hooks.initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            origin("hooks.initializer.cell"),
            cell,
            SemanticTerm::token(origin("hooks.token"), SemanticSortRef::int(), "0").unwrap(),
        )],
    )
    .unwrap();
    let theory = SemanticTheory::new(vec![SemanticModule::new(
        origin("hooks.module"),
        ModuleId::new("HOOKS").unwrap(),
        vec![],
        vec![
            SemanticSort::new(origin("hooks.g1"), g1),
            SemanticSort::new(origin("hooks.g2"), g2),
        ],
        vec![],
        productions,
        vec![],
        vec![],
        Some(configuration),
        vec![],
    )])
    .unwrap();
    let lowered = krs_compiler::lower_semantic_theory(&theory).unwrap();
    let emitted = krs_compiler::emit_k(&lowered).unwrap();
    for (index, operation) in HookOperation::ALL.into_iter().enumerate() {
        let marker = format!("Hook{index}(");
        let line = emitted
            .source()
            .lines()
            .find(|line| line.contains(&marker))
            .unwrap();
        let hook = line
            .split("hook(")
            .nth(1)
            .unwrap()
            .split(')')
            .next()
            .unwrap();
        assert_eq!(hook, operation.to_string(), "{operation:?}");
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Checks canonical grammar and builtin rule emission with one complete fixture."
)]
fn classified_grammar_and_builtin_rules_emit_canonical_k() {
    let expr = item("Expr", ItemKind::Sort);
    let id_sort = item("Id", ItemKind::Sort);
    let g1_point = item("G1Point", ItemKind::Sort);
    let eval = item("EvalInt", ItemKind::Constructor);
    let plus = item("Plus", ItemKind::Constructor);
    let bracket = item("ExprBracket", ItemKind::Constructor);
    let token = item("IdToken", ItemKind::Constructor);
    let keccak = item("Keccak256Raw", ItemKind::Constructor);
    let bn128_valid = item("Bn128Valid", ItemKind::Constructor);
    let bn128_add = item("Bn128Add", ItemKind::Constructor);
    let bn128_mul = item("Bn128Mul", ItemKind::Constructor);
    let point = item("Point", ItemKind::Constructor);
    let unary = ProductionGroupId::new("unary").unwrap();
    let additive = ProductionGroupId::new("additive").unwrap();

    let eval_production = SemanticProduction::new(
        origin("production.eval"),
        eval.clone(),
        SemanticSortRef::Declared(expr.clone()),
        vec![
            SemanticProductionItem::terminal(origin("eval.terminal"), "eval").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("eval.value"),
                ProductionFieldId::new("value").unwrap(),
                SemanticSortRef::Builtin(BuiltinSort::Int),
            ),
        ],
        vec![
            ProductionAttribute::Group {
                origin: origin("eval.group"),
                group: unary.clone(),
            },
            ProductionAttribute::Format {
                origin: origin("eval.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Literal(" ".into()),
                    FormatFragment::Item(2),
                    FormatFragment::Literal("%".into()),
                    FormatFragment::Newline,
                    FormatFragment::Indent,
                    FormatFragment::Dedent,
                ],
            },
            ProductionAttribute::Strictness {
                origin: origin("eval.strict"),
                kind: StrictnessKind::Strict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    origin("eval.strict.field"),
                    ProductionFieldId::new("value").unwrap(),
                )],
                result_sort: ProductionResultSort::new(
                    origin("eval.strict.result"),
                    SemanticSortRef::Builtin(BuiltinSort::Int),
                ),
            },
        ],
    )
    .unwrap();
    let plus_production = SemanticProduction::new(
        origin("production.plus"),
        plus,
        SemanticSortRef::Declared(expr.clone()),
        vec![
            SemanticProductionItem::non_terminal(
                origin("plus.lhs"),
                ProductionFieldId::new("lhs").unwrap(),
                SemanticSortRef::Declared(expr.clone()),
            ),
            SemanticProductionItem::terminal(origin("plus.terminal"), "+").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("plus.rhs"),
                ProductionFieldId::new("rhs").unwrap(),
                SemanticSortRef::Declared(expr.clone()),
            ),
        ],
        vec![
            ProductionAttribute::Group {
                origin: origin("plus.group"),
                group: additive.clone(),
            },
            ProductionAttribute::Strictness {
                origin: origin("plus.strict"),
                kind: StrictnessKind::SeqStrict,
                using: None,
                fields: vec![
                    ProductionFieldReference::new(
                        origin("plus.strict.field.0"),
                        ProductionFieldId::new("lhs").unwrap(),
                    ),
                    ProductionFieldReference::new(
                        origin("plus.strict.field.1"),
                        ProductionFieldId::new("rhs").unwrap(),
                    ),
                ],
                result_sort: ProductionResultSort::new(
                    origin("plus.strict.result"),
                    SemanticSortRef::Builtin(BuiltinSort::Int),
                ),
            },
        ],
    )
    .unwrap();
    let bracket_production = SemanticProduction::new(
        origin("production.bracket"),
        bracket,
        SemanticSortRef::Declared(expr.clone()),
        vec![
            SemanticProductionItem::terminal(origin("bracket.open"), "(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("bracket.value"),
                ProductionFieldId::new("value").unwrap(),
                SemanticSortRef::Declared(expr.clone()),
            ),
            SemanticProductionItem::terminal(origin("bracket.close"), ")").unwrap(),
        ],
        vec![ProductionAttribute::Bracket {
            origin: origin("bracket.attribute"),
        }],
    )
    .unwrap();
    let token_production = SemanticProduction::new(
        origin("production.token"),
        token,
        SemanticSortRef::Declared(id_sort.clone()),
        vec![
            SemanticProductionItem::regex_terminal(origin("token.regex"), None, "[a-z]+", None)
                .unwrap(),
        ],
        vec![ProductionAttribute::Token {
            origin: origin("token.attribute"),
            lexical_precedence: Some(2),
        }],
    )
    .unwrap();
    let hook_production = SemanticProduction::new(
        origin("production.keccak"),
        keccak,
        SemanticSortRef::Builtin(BuiltinSort::Bytes),
        vec![
            SemanticProductionItem::terminal(origin("keccak.open"), "Keccak256raw(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("keccak.value"),
                ProductionFieldId::new("value").unwrap(),
                SemanticSortRef::Builtin(BuiltinSort::Bytes),
            ),
            SemanticProductionItem::terminal(origin("keccak.close"), ")").unwrap(),
        ],
        vec![
            ProductionAttribute::Function {
                origin: origin("keccak.function"),
            },
            ProductionAttribute::Total {
                origin: origin("keccak.total"),
            },
            ProductionAttribute::Hook {
                origin: origin("keccak.hook"),
                operation: HookOperation::KryptoKeccak256Raw,
            },
        ],
    )
    .unwrap();
    let point_production = SemanticProduction::new(
        origin("production.point"),
        point,
        SemanticSortRef::Declared(g1_point.clone()),
        vec![
            SemanticProductionItem::terminal(origin("point.open"), "(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("point.x"),
                ProductionFieldId::new("x").unwrap(),
                SemanticSortRef::Builtin(BuiltinSort::Int),
            ),
            SemanticProductionItem::terminal(origin("point.comma"), ",").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("point.y"),
                ProductionFieldId::new("y").unwrap(),
                SemanticSortRef::Builtin(BuiltinSort::Int),
            ),
            SemanticProductionItem::terminal(origin("point.close"), ")").unwrap(),
        ],
        vec![],
    )
    .unwrap();
    let bn128_valid_production = SemanticProduction::new(
        origin("production.bn128-valid"),
        bn128_valid,
        SemanticSortRef::Builtin(BuiltinSort::Bool),
        vec![
            SemanticProductionItem::terminal(origin("bn128-valid.open"), "Bn128Valid(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("bn128-valid.point"),
                ProductionFieldId::new("point").unwrap(),
                SemanticSortRef::Declared(g1_point.clone()),
            ),
            SemanticProductionItem::terminal(origin("bn128-valid.close"), ")").unwrap(),
        ],
        vec![
            ProductionAttribute::Function {
                origin: origin("bn128-valid.function"),
            },
            ProductionAttribute::Total {
                origin: origin("bn128-valid.total"),
            },
            ProductionAttribute::Hook {
                origin: origin("bn128-valid.hook"),
                operation: HookOperation::KryptoBn128Valid,
            },
        ],
    )
    .unwrap();
    let bn128_add_production = SemanticProduction::new(
        origin("production.bn128-add"),
        bn128_add,
        SemanticSortRef::Declared(g1_point.clone()),
        vec![
            SemanticProductionItem::terminal(origin("bn128-add.open"), "Bn128Add(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("bn128-add.left"),
                ProductionFieldId::new("left").unwrap(),
                SemanticSortRef::Declared(g1_point.clone()),
            ),
            SemanticProductionItem::terminal(origin("bn128-add.comma"), ",").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("bn128-add.right"),
                ProductionFieldId::new("right").unwrap(),
                SemanticSortRef::Declared(g1_point.clone()),
            ),
            SemanticProductionItem::terminal(origin("bn128-add.close"), ")").unwrap(),
        ],
        vec![
            ProductionAttribute::Function {
                origin: origin("bn128-add.function"),
            },
            ProductionAttribute::Total {
                origin: origin("bn128-add.total"),
            },
            ProductionAttribute::Hook {
                origin: origin("bn128-add.hook"),
                operation: HookOperation::KryptoBn128Add,
            },
        ],
    )
    .unwrap();
    let bn128_mul_production = SemanticProduction::new(
        origin("production.bn128-mul"),
        bn128_mul,
        SemanticSortRef::Declared(g1_point.clone()),
        vec![
            SemanticProductionItem::terminal(origin("bn128-mul.open"), "Bn128Mul(").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("bn128-mul.point"),
                ProductionFieldId::new("point").unwrap(),
                SemanticSortRef::Declared(g1_point.clone()),
            ),
            SemanticProductionItem::terminal(origin("bn128-mul.comma"), ",").unwrap(),
            SemanticProductionItem::non_terminal(
                origin("bn128-mul.scalar"),
                ProductionFieldId::new("scalar").unwrap(),
                SemanticSortRef::Builtin(BuiltinSort::Int),
            ),
            SemanticProductionItem::terminal(origin("bn128-mul.close"), ")").unwrap(),
        ],
        vec![
            ProductionAttribute::Function {
                origin: origin("bn128-mul.function"),
            },
            ProductionAttribute::Total {
                origin: origin("bn128-mul.total"),
            },
            ProductionAttribute::Hook {
                origin: origin("bn128-mul.hook"),
                operation: HookOperation::KryptoBn128Mul,
            },
        ],
    )
    .unwrap();

    let pgm = SemanticId::new("PGM").unwrap();
    let lhs = SemanticTerm::application(
        origin("rule.lhs"),
        SemanticSortRef::Declared(expr.clone()),
        ApplicationRef::Declared(eval),
        vec![SemanticTerm::variable(
            origin("rule.x.left"),
            SemanticSortRef::Builtin(BuiltinSort::Int),
            pgm.clone(),
        )],
    );
    let rhs = SemanticTerm::application(
        origin("rule.rhs"),
        SemanticSortRef::Builtin(BuiltinSort::Int),
        ApplicationRef::Builtin(BuiltinOperation::IntAdd),
        vec![
            SemanticTerm::variable(
                origin("rule.x.right"),
                SemanticSortRef::Builtin(BuiltinSort::Int),
                pgm.clone(),
            ),
            SemanticTerm::token(
                origin("rule.one"),
                SemanticSortRef::Builtin(BuiltinSort::Int),
                "1",
            )
            .unwrap(),
        ],
    );
    let rule = SemanticRule::new(
        origin("rule"),
        item("eval_int", ItemKind::Rule),
        SentenceKind::Transition,
        vec![SemanticVariable::new(
            pgm.clone(),
            SemanticSortRef::Builtin(BuiltinSort::Int),
        )],
        SemanticTerm::rewrite(
            origin("rule.rewrite"),
            SemanticSortRef::Declared(expr.clone()),
            lhs,
            rhs,
        )
        .unwrap(),
    )
    .unwrap();
    let k_cell = SemanticId::new("machine.k").unwrap();
    let configuration = FixedConfiguration::new(
        origin("configuration"),
        SemanticId::new("machine").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                origin("cell"),
                k_cell.clone(),
                "k",
                vec![],
                SemanticSortRef::k_sequence(),
            )
            .unwrap(),
        ],
        origin("initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![
            FixedConfigurationVariable::new(
                origin("initializer.variable"),
                pgm.clone(),
                "PGM",
                SemanticSortRef::Declared(expr.clone()),
                true,
            )
            .unwrap(),
        ],
        vec![FixedInitializerCell::term(
            origin("initializer.k"),
            k_cell,
            SemanticTerm::k_sequence(
                origin("initializer.sequence"),
                SemanticSortRef::Declared(expr.clone()),
                vec![SemanticTerm::variable(
                    origin("initializer.program"),
                    SemanticSortRef::Declared(expr.clone()),
                    pgm,
                )],
            ),
        )],
    )
    .unwrap();
    let module = SemanticModule::new(
        origin("module"),
        ModuleId::new("KRS-GRAMMAR-LOWERING").unwrap(),
        vec![],
        vec![
            SemanticSort::new(origin("sort.expr"), expr.clone()),
            SemanticSort::new(origin("sort.id"), id_sort),
            SemanticSort::new(origin("sort.g1-point"), g1_point),
        ],
        vec![SemanticSubsort::new(
            origin("subsort.int-expr"),
            SemanticSortRef::Builtin(BuiltinSort::Int),
            SemanticSortRef::Declared(expr),
        )],
        vec![
            eval_production,
            plus_production,
            bracket_production,
            token_production,
            hook_production,
            point_production,
            bn128_valid_production,
            bn128_add_production,
            bn128_mul_production,
        ],
        vec![
            PrecedenceRelation::new(origin("precedence"), vec![unary], vec![additive.clone()])
                .unwrap(),
        ],
        vec![
            GroupAssociativitySentence::new(
                origin("associativity"),
                GroupAssociativity::Left,
                vec![additive],
            )
            .unwrap(),
        ],
        Some(configuration),
        vec![rule],
    );
    let theory = SemanticTheory::new(vec![module]).unwrap();
    let (_lowered, emitted) = assert_lowering_contract(&theory);
    let source = emitted.source().to_owned();
    assert!(source.contains("  imports INT\n"));
    assert!(source.contains("r\"[a-z]+\" [token, prec(2)]"));
    assert!(
        !source.contains("symbol(idToken)"),
        "a token production denotes domain values and must not declare a constructor symbol"
    );
    assert!(source.contains("group(krsgroup-"));
    assert!(source.contains("syntax priority krsgroup-"));
    assert!(source.contains("syntax left krsgroup-"));
    assert!(source.contains("bracket, format(%1%2%3)"));
    assert!(source.contains("format(%1 %2%%%n%i%d)"));
    assert!(source.contains("strict, result(Int)"));
    assert!(source.contains("seqstrict, result(Int)"));
    assert!(source.contains(", function, total, hook(KRYPTO.keccak256raw)]"));
    assert!(source.contains(", function, total, hook(KRYPTO.bn128valid)]"));
    assert!(source.contains(", function, total, hook(KRYPTO.bn128add)]"));
    assert!(source.contains(", function, total, hook(KRYPTO.bn128mul)]"));
    assert!(source.contains("+Int 1"));
    let configuration = source
        .lines()
        .find(|line| line.trim_start().starts_with("<k> "))
        .unwrap();
    assert!(source.contains("  configuration\n"));
    assert!(configuration.starts_with("    <k> $PGM:"));
    assert!(configuration.ends_with(" </k>"));
    assert!(!configuration.contains("V50474D"));
    assert!(source.contains("V50474D:Int +Int 1"));
    assert!(!source.contains("$PGM:Int +Int 1"));
}
