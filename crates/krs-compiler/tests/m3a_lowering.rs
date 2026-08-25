//! Protocol-v6 grammar reaches Definition IR and canonical K source.

use krs_compiler::{emit_k, lower_semantic_theory};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, FormatFragment, GroupAssociativity,
    GroupAssociativitySentence, ItemKind, ModuleId, NodeOrigin, OriginStack, PackageId,
    PrecedenceRelation, ProductionAttribute, ProductionFieldId, ProductionFieldReference,
    ProductionGroupId, ProductionResultSort, SemanticCell, SemanticConfiguration, SemanticId,
    SemanticInitializer, SemanticModule, SemanticProduction, SemanticProductionItem, SemanticRule,
    SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm, SemanticTheory, SemanticVariable,
    SentenceKind, Sha256Digest, SourceFileId, SourceMapKey, SourceRange, StableItemId,
    StrictnessKind,
};

fn package() -> PackageId {
    PackageId::new("KRS-M3A", "m3a", "0.1.0", "workspace").unwrap()
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), ["expr"], name, kind, "").unwrap()
}

fn origin(key: &str) -> NodeOrigin {
    let file = SourceFileId::new(
        package(),
        "src/expr.rs",
        Sha256Digest::new("1".repeat(64)).unwrap(),
    )
    .unwrap();
    NodeOrigin::new(
        SourceMapKey::new(key).unwrap(),
        OriginStack::authored(SourceRange::new(file, 0, 1).unwrap()),
    )
}

#[test]
#[allow(clippy::too_many_lines)]
fn classified_grammar_and_builtin_rules_emit_canonical_k() {
    let expr = item("Expr", ItemKind::Sort);
    let id_sort = item("Id", ItemKind::Sort);
    let eval = item("EvalInt", ItemKind::Constructor);
    let plus = item("Plus", ItemKind::Constructor);
    let bracket = item("ExprBracket", ItemKind::Constructor);
    let token = item("IdToken", ItemKind::Constructor);
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
    let configuration = SemanticConfiguration::new(
        origin("configuration"),
        SemanticId::new("machine").unwrap(),
        SemanticCell::new(
            origin("cell"),
            SemanticId::new("machine.k").unwrap(),
            "k",
            SemanticSortRef::k_sequence(),
        )
        .unwrap(),
        SemanticInitializer::new(
            origin("initializer"),
            SemanticId::new("machine.init").unwrap(),
            vec![SemanticVariable::new(
                pgm.clone(),
                SemanticSortRef::Declared(expr.clone()),
            )],
            SemanticTerm::k_sequence(
                origin("initializer.sequence"),
                SemanticSortRef::Declared(expr.clone()),
                vec![SemanticTerm::variable(
                    origin("initializer.program"),
                    SemanticSortRef::Declared(expr.clone()),
                    pgm,
                )],
            ),
        ),
    );
    let module = SemanticModule::new(
        origin("module"),
        ModuleId::new("KRS-M3A-LOWERING").unwrap(),
        vec![],
        vec![
            SemanticSort::new(origin("sort.expr"), expr.clone()),
            SemanticSort::new(origin("sort.id"), id_sort),
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
    let lowered = lower_semantic_theory(&theory).unwrap();
    let source = emit_k(&lowered).unwrap().source().to_owned();
    assert!(source.contains("  imports INT\n"));
    assert!(source.contains("r\"[a-z]+\" [symbol(idToken), token, prec(2)]"));
    assert!(source.contains("group(krsgroup-"));
    assert!(source.contains("syntax priority krsgroup-"));
    assert!(source.contains("syntax left krsgroup-"));
    assert!(source.contains("bracket, format(%1%2%3)"));
    assert!(source.contains("format(%1 %2%%%n%i%d)"));
    assert!(source.contains("strict, result(Int)"));
    assert!(source.contains("seqstrict, result(Int)"));
    assert!(source.contains("+Int 1"));
    let configuration = source
        .lines()
        .find(|line| line.trim_start().starts_with("configuration "))
        .unwrap();
    assert!(configuration.starts_with("  configuration <k> $PGM:"));
    assert!(configuration.ends_with(" </k>"));
    assert!(!configuration.contains("V50474D"));
    assert!(source.contains("V50474D:Int +Int 1"));
    assert!(!source.contains("$PGM:Int +Int 1"));
}
