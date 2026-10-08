//! Contract tests for centralized compiler-generated production identities.

use std::collections::BTreeSet;

use krs_ir::testing;
use krs_ir::{
    GeneratedProductionIdError, GeneratedProductionKind, ItemKind, PackageId, StableItemId,
    TokenProductionContent, generated_production_id,
};

fn package(namespace: &str, name: &str) -> PackageId {
    testing::package_with(namespace, name, "1.2.3", "workspace")
}

fn grammar(package: PackageId, modules: &[&str], name: &str, disambiguator: &str) -> StableItemId {
    StableItemId::new(
        package,
        modules.iter().copied(),
        name,
        ItemKind::Grammar,
        disambiguator,
    )
    .unwrap()
}

const TOKEN: GeneratedProductionKind<'static> = GeneratedProductionKind::Token {
    content: TokenProductionContent::Regex("[a-z]+"),
};

#[test]
fn derivation_has_a_fixed_auditable_encoding() {
    let source = grammar(
        package("IMP", "imp-semantics"),
        &["syntax", "expression"],
        "Identifier",
        "lexical-0",
    );

    let token = generated_production_id(&source, TOKEN).unwrap();

    assert_eq!(token.package(), source.package());
    assert_eq!(token.module_path(), source.module_path());
    assert_eq!(token.item_kind(), ItemKind::Constructor);
    assert_eq!(token.item_name(), "__krs_generated_semantic_production");
    assert_eq!(
        token.disambiguator(),
        "krs-generated-production-v1:token:regex:5b612d7a5d2b:4964656e746966696572:6c65786963616c2d30"
    );
}

#[test]
fn token_productions_of_one_carrier_are_keyed_by_content() {
    let source = grammar(package("IMP", "imp"), &["syntax"], "Name", "");
    let regex = generated_production_id(&source, TOKEN).unwrap();
    let terminal = generated_production_id(
        &source,
        GeneratedProductionKind::Token {
            content: TokenProductionContent::Terminal("[a-z]+"),
        },
    )
    .unwrap();
    let other = generated_production_id(
        &source,
        GeneratedProductionKind::Token {
            content: TokenProductionContent::Regex("[A-Z]+"),
        },
    )
    .unwrap();
    assert_ne!(regex, terminal);
    assert_ne!(regex, other);
}

#[test]
fn derivation_is_deterministic_and_adapter_neutral() {
    let source = grammar(package("IMP", "imp"), &["syntax"], "Int", "");

    let first = generated_production_id(&source, TOKEN).unwrap();
    let second = generated_production_id(&source, TOKEN).unwrap();
    let round_trip: StableItemId =
        serde_json::from_str(&serde_json::to_string(&first).unwrap()).unwrap();

    assert_eq!(first, second);
    assert_eq!(first, round_trip);
}

#[test]
fn token_and_bracket_domains_cannot_collide() {
    let source = grammar(package("IMP", "imp"), &["syntax"], "Expression", "0");

    let token = generated_production_id(&source, TOKEN).unwrap();
    let bracket = generated_production_id(&source, GeneratedProductionKind::Bracket).unwrap();

    assert_ne!(token, bracket);
    assert!(token.disambiguator().contains(":token:"));
    assert!(bracket.disambiguator().contains(":bracket:"));
}

#[test]
fn every_stable_source_component_participates_in_identity() {
    let sources = [
        grammar(package("IMP", "imp"), &["syntax"], "Expr", ""),
        grammar(package("IMP-ALT", "imp"), &["syntax"], "Expr", ""),
        grammar(package("IMP", "imp-alt"), &["syntax"], "Expr", ""),
        grammar(package("IMP", "imp"), &["nested", "syntax"], "Expr", ""),
        grammar(package("IMP", "imp"), &["syntax"], "ExprAlt", ""),
        grammar(package("IMP", "imp"), &["syntax"], "Expr", "1"),
    ];

    let generated = sources
        .iter()
        .flat_map(|source| {
            [
                generated_production_id(source, TOKEN).unwrap(),
                generated_production_id(source, GeneratedProductionKind::Bracket).unwrap(),
            ]
        })
        .collect::<BTreeSet<_>>();

    assert_eq!(generated.len(), sources.len() * 2);
}

#[test]
fn component_boundaries_and_unicode_are_injective() {
    let sources = [
        grammar(package("IMP", "imp"), &["syntax"], "ab", "c"),
        grammar(package("IMP", "imp"), &["syntax"], "a", "bc"),
        grammar(package("IMP", "imp"), &["syntax"], "a:b", "c"),
        grammar(package("IMP", "imp"), &["syntax"], "a", "b:c"),
        grammar(package("IMP", "imp"), &["syntax"], "式", "括弧"),
        grammar(package("IMP", "imp"), &["syntax"], "式括", "弧"),
        grammar(package("IMP", "imp"), &["syntax"], "path/like", ""),
        grammar(package("IMP", "imp"), &["syntax"], "path\\like", ""),
    ];

    let generated = sources
        .iter()
        .map(|source| generated_production_id(source, GeneratedProductionKind::Bracket).unwrap())
        .collect::<BTreeSet<_>>();

    assert_eq!(generated.len(), sources.len());
    assert!(
        generated
            .iter()
            .all(|id| { !id.disambiguator().contains('/') && !id.disambiguator().contains('\\') })
    );
}

#[test]
fn authored_declarations_are_rejected_as_derivation_sources() {
    let sort = StableItemId::new(
        package("IMP", "imp"),
        ["syntax"],
        "Expression",
        ItemKind::Sort,
        "",
    )
    .unwrap();

    assert_eq!(
        generated_production_id(&sort, TOKEN),
        Err(GeneratedProductionIdError::ExpectedGrammarDescriptor {
            actual: ItemKind::Sort
        })
    );
}
