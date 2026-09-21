use k_rust_backend::{
    definition::BackendDefinition,
    rule::{CellIndex, rule_index, subject_index},
    term::Name,
};
use k_rust_kore::kore::{
    ast::KoreString,
    parser::{parse_definition, parse_pattern},
};

use super::support::internal_term;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
        module MAIN
          sort SortK{} []
          sort SortKItem{} []
          sort SortToken{} [hasDomainValues{}()]
          sort SortKCell{} []
          sort SortGeneratedTopCell{} []
          symbol inj{From, To}(From) : To [sortInjection{}()]
          symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), total{}()]
          symbol dotk{}() : SortK{} [constructor{}(), total{}()]
          symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}(), total{}()]
          symbol top{}(SortKCell{}) : SortGeneratedTopCell{} [constructor{}(), total{}()]
          symbol A{}() : SortKItem{} [constructor{}(), total{}()]
          symbol B{}() : SortKItem{} [constructor{}(), total{}()]
          symbol f{}() : SortKItem{} [function{}(), total{}()]
        endmodule []"#,
    )
    .expect("index definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("index definition should internalize")
}

fn indexed(definition: &BackendDefinition, head: &str) -> k_rust_backend::term::Term {
    internal_term(
        definition,
        &format!("top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, dotk{{}}())))"),
    )
}

#[test]
fn anything_is_the_covering_top_and_none_covers_nothing() {
    let concrete = CellIndex::Constructor(Name::from("A"));
    assert!(CellIndex::Anything.covers(&concrete));
    assert!(concrete.covers(&concrete));
    assert!(!CellIndex::None.covers(&CellIndex::None));
    assert!(!CellIndex::None.covers(&concrete));
}

#[test]
fn meet_is_commutative_idempotent_and_rejects_conflicts() {
    let a = CellIndex::Constructor(Name::from("A"));
    let b = CellIndex::Constructor(Name::from("B"));
    assert_eq!(a.clone().meet(a.clone()), a);
    assert_eq!(CellIndex::Anything.meet(a.clone()), a);
    assert_eq!(a.clone().meet(b.clone()), CellIndex::None);
    assert_eq!(
        a.meet(b.clone()),
        b.meet(CellIndex::Constructor(Name::from("A")))
    );
}

#[test]
fn indexes_the_injection_stripped_k_sequence_head() {
    let definition = definition();
    let term = indexed(&definition, "inj{SortKItem{}, SortKItem{}}(A{}())");
    assert_eq!(
        rule_index(&definition, &term).cells(),
        &[CellIndex::Constructor(Name::from("A"))]
    );
}

#[test]
fn subject_functions_are_wildcards_but_rule_functions_are_not() {
    let definition = definition();
    let term = indexed(&definition, "f{}()");
    assert_eq!(
        rule_index(&definition, &term).cells(),
        &[CellIndex::Function(Name::from("f"))]
    );
    assert_eq!(
        subject_index(&definition, &term).cells(),
        &[CellIndex::Anything]
    );
}

#[test]
fn indexes_domain_values_without_losing_bytes() {
    let definition = definition();
    let syntax = parse_pattern(
        r#"top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortToken{}, SortKItem{}}(\dv{SortToken{}}("\xff")), dotk{}())))"#,
    )
    .expect("byte-preserving subject should parse");
    let term = definition
        .internalize_frontend_term(&syntax, &[])
        .expect("frontend-validated injection should internalize");
    assert_eq!(
        rule_index(&definition, &term).cells(),
        &[CellIndex::Value(KoreString::from(vec![0xff]))]
    );
}

#[test]
fn absent_or_unstructured_k_cells_are_wildcards() {
    let definition = definition();
    let absent = internal_term(&definition, "A{}()");
    let malformed = internal_term(&definition, "top{}(Lbl'-LT-'k'-GT-'{}(dotk{}()))");
    assert_eq!(
        rule_index(&definition, &absent).cells(),
        &[CellIndex::Anything]
    );
    assert_eq!(
        rule_index(&definition, &malformed).cells(),
        &[CellIndex::Constructor(Name::from("dotk"))]
    );
}
