use std::collections::BTreeMap;

use krs_ir::{
    Arguments, BuiltinOperation, BuiltinOperator, DescriptorApplicationHeadClass,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorLiteral, DescriptorTerm,
    ItemKind, ListOperation, OperatorDomain, PackageId, ProvenanceKey, SentenceKind, StableItemId,
};
use krs_ir_levels::SemanticSortRef;
use krs_syntax::ProvenanceRole;

use super::{Patterns, matches_evaluated_terms};
use crate::semantic::catalog::ProductionSignature;

fn item(name: &str) -> StableItemId {
    StableItemId::new(
        PackageId::new("FUNCTION-PATTERNS", "function-patterns", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        ItemKind::Constructor,
        "",
    )
    .unwrap()
}

/// `Hold` and `Pair`, constructors, and `Size`, a function.
fn catalog() -> BTreeMap<StableItemId, ProductionSignature> {
    let signature = |function| ProductionSignature {
        result_sort: SemanticSortRef::Declared(item("Stmt")),
        fields: Vec::new(),
        token: false,
        parameters: Vec::new(),
        function,
        cons_list_empty: None,
    };
    [
        (item("Hold"), signature(false)),
        (item("Pair"), signature(false)),
        (item("Size"), signature(true)),
    ]
    .into()
}

/// The head key of every application, told apart by `ordinal`.
fn head(ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(ProvenanceRole::RuleLeftApplicationHead, ordinal)
}

fn other_key() -> ProvenanceKey {
    ProvenanceKey::new(ProvenanceRole::RuleLeftReference, 0)
}

fn apply(
    application: DescriptorApplicationRef,
    ordinal: u32,
    arguments: Vec<DescriptorTerm>,
) -> DescriptorTerm {
    DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: head(ordinal),
            application,
        },
        path_key: other_key(),
        arguments: Arguments::Positional(arguments.into_iter().map(Box::new).collect()),
        instance: Vec::new(),
        update: None,
        open: false,
    }
}

fn declared(name: &str, ordinal: u32, arguments: Vec<DescriptorTerm>) -> DescriptorTerm {
    apply(
        DescriptorApplicationRef::Declared(item(name)),
        ordinal,
        arguments,
    )
}

fn x() -> DescriptorTerm {
    DescriptorTerm::Variable {
        key: other_key(),
        path_key: other_key(),
        name: "x".into(),
    }
}

fn one() -> DescriptorTerm {
    DescriptorTerm::Literal {
        key: other_key(),
        literal: DescriptorLiteral::Int("1".into()),
    }
}

/// `Size(x)`, at head ordinal 9.
fn size() -> DescriptorTerm {
    declared("Size", 9, vec![x()])
}

fn rewrite(from: DescriptorTerm, to: DescriptorTerm) -> DescriptorTerm {
    DescriptorTerm::Rewrite {
        key: other_key(),
        from_key: other_key(),
        to_key: other_key(),
        from: Box::new(from),
        to: Some(Box::new(to)),
    }
}

/// The head ordinal of the application the pattern rooted at `term` refuses.
fn refused(term: &DescriptorTerm) -> Option<u32> {
    let catalog = catalog();
    Patterns { catalog: &catalog }
        .root(term)
        .err()
        .map(|(reference, _)| reference.key.ordinal())
}

#[test]
fn a_function_below_the_root_is_refused_at_its_head() {
    assert_eq!(refused(&declared("Hold", 0, vec![size()])), Some(9));
    assert_eq!(
        refused(&declared(
            "Pair",
            0,
            vec![x(), declared("Hold", 1, vec![size()])]
        )),
        Some(9)
    );
}

#[test]
fn the_root_of_a_pattern_may_apply_a_function() {
    // An equation's root is the function it defines.
    assert_eq!(refused(&size()), None);
    assert_eq!(refused(&declared("Hold", 0, vec![x()])), None);
}

#[test]
fn a_builtin_function_and_an_operator_are_functions() {
    let add = apply(
        DescriptorApplicationRef::Builtin(BuiltinOperation::IntAdd),
        9,
        vec![one(), one()],
    );
    assert_eq!(refused(&declared("Hold", 0, vec![add])), Some(9));
    let plus = apply(
        DescriptorApplicationRef::Operator(BuiltinOperator::Add),
        9,
        vec![x(), one()],
    );
    assert_eq!(refused(&declared("Hold", 0, vec![plus])), Some(9));
    // `LE` is the constructor of a byte order, matched as written.
    let little = apply(
        DescriptorApplicationRef::Builtin(BuiltinOperation::BytesLittleEndian),
        9,
        Vec::new(),
    );
    assert_eq!(refused(&declared("Hold", 0, vec![little])), None);
}

#[test]
fn every_operator_reading_is_a_builtin_function() {
    for operator in BuiltinOperator::ALL {
        for domain in OperatorDomain::ALL {
            if let Some(reading) = operator.reading(domain) {
                assert!(
                    reading.operation().is_functional(),
                    "{} on {domain:?}",
                    operator.symbol()
                );
            }
        }
    }
}

#[test]
fn a_collection_entry_may_apply_a_function() {
    let element = apply(
        DescriptorApplicationRef::List(ListOperation::Item),
        5,
        vec![size()],
    );
    assert_eq!(refused(&declared("Hold", 0, vec![element])), None);
    // A collection's other operations are its functions.
    let length = apply(
        DescriptorApplicationRef::List(ListOperation::Size),
        5,
        vec![x()],
    );
    assert_eq!(refused(&declared("Hold", 0, vec![length])), Some(5));
}

#[test]
fn a_rewrite_matches_its_left_side_and_builds_its_right_side() {
    let built = rewrite(x(), size());
    assert_eq!(refused(&declared("Hold", 0, vec![built])), None);
    let matched = rewrite(size(), x());
    assert_eq!(refused(&declared("Hold", 0, vec![matched])), Some(9));
    // A rewrite at the root rewrites the subject's root.
    assert_eq!(refused(&rewrite(size(), x())), None);
}

#[test]
fn an_alias_and_alternatives_stand_where_they_are_written() {
    let alias = |pattern| DescriptorTerm::As {
        key: other_key(),
        binding_key: other_key(),
        name: "y".into(),
        pattern: Box::new(pattern),
    };
    assert_eq!(refused(&alias(size())), None);
    assert_eq!(refused(&declared("Hold", 0, vec![alias(size())])), Some(9));
    let alternatives = DescriptorTerm::Or {
        key: other_key(),
        alternatives: vec![declared("Hold", 1, vec![x()]), size()]
            .try_into()
            .unwrap(),
    };
    assert_eq!(refused(&declared("Hold", 0, vec![alternatives])), Some(9));
}

#[test]
fn only_rules_and_equations_match_evaluated_terms() {
    for kind in [SentenceKind::Transition, SentenceKind::Equation] {
        assert!(matches_evaluated_terms(kind, false), "{kind:?}");
        // A readable or `cells!` claim is a transition-shaped claim.
        assert!(!matches_evaluated_terms(kind, true), "{kind:?} claim");
    }
    for kind in [
        SentenceKind::Simplification,
        SentenceKind::Claim,
        SentenceKind::Alias,
        SentenceKind::Desugar,
        SentenceKind::Context,
    ] {
        assert!(!matches_evaluated_terms(kind, false), "{kind:?}");
    }
}
