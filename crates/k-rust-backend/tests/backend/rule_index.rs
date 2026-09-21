use k_rust_backend::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{
        CellIndex, IndexedRewriteRule, TermIndex, applicable_rewrite_groups, rule_index,
        subject_index, term_index,
    },
    term::Name,
};
use k_rust_kore::kore::{
    ast::KoreString,
    parser::{parse_definition, parse_pattern},
};
use proptest::prelude::*;

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
          axiom{} \rewrites{SortGeneratedTopCell{}}(
            \and{SortGeneratedTopCell{}}(
              top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(A{}(), dotk{}()))),
              \top{SortGeneratedTopCell{}}()
            ),
            top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(B{}(), dotk{}())))
          ) [label{}("A-first"), priority{}("50")]
          axiom{} \rewrites{SortGeneratedTopCell{}}(
            \and{SortGeneratedTopCell{}}(
              top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(B{}(), dotk{}()))),
              \top{SortGeneratedTopCell{}}()
            ),
            top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(A{}(), dotk{}())))
          ) [label{}("B-only"), priority{}("50")]
          axiom{} \rewrites{SortGeneratedTopCell{}}(
            \and{SortGeneratedTopCell{}}(
              top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(A{}(), dotk{}()))),
              \top{SortGeneratedTopCell{}}()
            ),
            top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(A{}(), dotk{}())))
          ) [label{}("A-second"), priority{}("50")]
          axiom{} \rewrites{SortGeneratedTopCell{}}(
            \and{SortGeneratedTopCell{}}(
              top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(X:SortKItem{}, dotk{}()))),
              \top{SortGeneratedTopCell{}}()
            ),
            top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(X:SortKItem{}, dotk{}())))
          ) [label{}("wild"), priority{}("50")]
        endmodule []"#,
    )
    .expect("index definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("index definition should internalize")
}

fn old_candidates<'a>(
    definition: &'a BackendDefinition,
    index: &TermIndex,
) -> Vec<&'a IndexedRewriteRule> {
    let covered = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    covered
        .into_iter()
        .filter_map(|covered| definition.rewrite_theory.get(covered))
        .flat_map(|groups| groups.values())
        .flatten()
        .collect()
}

fn candidate_ids(
    definition: &BackendDefinition,
    subject: &k_rust_backend::term::Term,
) -> Vec<String> {
    applicable_rewrite_groups(
        &definition.rewrite_theory,
        &term_index(subject),
        &subject_index(definition, subject),
    )
    .into_values()
    .flatten()
    .map(|rule| rule.attributes.unique_id.clone())
    .collect()
}

fn indexed(definition: &BackendDefinition, head: &str) -> k_rust_backend::term::Term {
    internal_term(
        definition,
        &format!("top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, dotk{{}}())))"),
    )
}

#[test]
fn anything_on_either_side_disables_filtering_and_none_covers_nothing() {
    let concrete = CellIndex::Constructor(Name::from("A"));
    assert!(CellIndex::Anything.covers(&concrete));
    assert!(concrete.covers(&CellIndex::Anything));
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
    assert_eq!(
        candidate_ids(&definition, &term),
        ["A-first", "B-only", "A-second", "wild"]
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

#[test]
fn filtering_keeps_priority_and_declaration_order() {
    let definition = definition();
    let subject = indexed(&definition, "A{}()");
    assert_eq!(
        candidate_ids(&definition, &subject),
        ["A-first", "A-second", "wild"]
    );
}

proptest! {
    #[test]
    fn indexed_candidates_equal_the_old_sequence_filtered_by_coverage(use_a in any::<bool>()) {
        let definition = definition();
        let subject = indexed(&definition, if use_a { "A{}()" } else { "B{}()" });
        let subject_index = subject_index(&definition, &subject);
        let expected = old_candidates(&definition, &term_index(&subject))
            .into_iter()
            .filter(|stored| stored.index.covers(&subject_index))
            .map(|stored| stored.attributes.unique_id.clone())
            .collect::<Vec<_>>();
        prop_assert_eq!(candidate_ids(&definition, &subject), expected);
    }

    #[test]
    fn every_filtered_rigid_head_would_have_failed_matching(use_a in any::<bool>()) {
        let definition = definition();
        let subject = indexed(&definition, if use_a { "A{}()" } else { "B{}()" });
        let subject_index = subject_index(&definition, &subject);
        for stored in old_candidates(&definition, &term_index(&subject)) {
            if !stored.index.covers(&subject_index) {
                prop_assert!(matches!(
                    match_terms_in_definition(
                        MatchMode::Rewrite,
                        &definition,
                        &stored.lhs,
                        &subject,
                    ),
                    MatchResult::Failed(_)
                ));
            }
        }
    }
}
