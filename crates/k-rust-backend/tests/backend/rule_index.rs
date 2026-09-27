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
    definition_with("")
}

fn definition_with(extra_axioms: &str) -> BackendDefinition {
    let syntax = parse_definition(
        &(r#"[]
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
        "#
        .to_owned()
            + extra_axioms
            + "endmodule []"),
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
fn anything_on_either_side_disables_filtering_and_none_covers_only_anything() {
    let concrete = CellIndex::Constructor(Name::from("A"));
    assert!(CellIndex::Anything.covers(&concrete));
    assert!(concrete.covers(&CellIndex::Anything));
    assert!(concrete.covers(&concrete));
    assert!(!CellIndex::None.covers(&CellIndex::None));
    assert!(!CellIndex::None.covers(&concrete));
    assert!(CellIndex::None.covers(&CellIndex::Anything));
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

/// A conjunction's key covers every subject key both conjuncts' keys cover, and a function
/// conjunct, keyed `Anything` since the matcher evaluates or defers it, leaves the other key.
#[test]
fn meet_covers_what_both_conjuncts_cover() {
    let keys = [
        CellIndex::None,
        CellIndex::Anything,
        CellIndex::Constructor(Name::from("A")),
        CellIndex::Constructor(Name::from("B")),
        CellIndex::Overloaded,
        CellIndex::Anywhere(Name::from("h")),
        CellIndex::Anywhere(Name::from("i")),
        CellIndex::Value(KoreString::from(b"1".to_vec())),
        CellIndex::Map,
        CellIndex::List,
        CellIndex::Set,
    ];
    for left in &keys {
        for right in &keys {
            let meet = left.clone().meet(right.clone());
            assert_eq!(
                meet,
                right.clone().meet(left.clone()),
                "{left:?} /\\ {right:?}"
            );
            for subject in &keys {
                if left.covers(subject) && right.covers(subject) {
                    assert!(
                        meet.covers(subject),
                        "{left:?} /\\ {right:?} = {meet:?} drops {subject:?}"
                    );
                }
            }
        }
    }
    let a = CellIndex::Constructor(Name::from("A"));
    assert_eq!(CellIndex::Anything.meet(a.clone()), a);
    assert_eq!(
        CellIndex::Overloaded.meet(CellIndex::Anywhere(Name::from("h"))),
        CellIndex::Overloaded
    );
}

#[test]
fn indexes_the_injection_stripped_k_sequence_head() {
    let definition = definition();
    let term = indexed(&definition, "inj{SortKItem{}, SortKItem{}}(A{}())");
    assert_eq!(
        rule_index(&definition, &term).cells(),
        &[CellIndex::Constructor(Name::from("A")), CellIndex::Anything]
    );
}

#[test]
fn functions_are_wildcards_and_anywhere_heads_are_rigid_only_in_rules() {
    let definition = definition();
    let term = indexed(&definition, "f{}()");
    assert_eq!(
        rule_index(&definition, &term).cells(),
        &[CellIndex::Anything, CellIndex::Anything]
    );
    assert_eq!(
        subject_index(&definition, &term).cells(),
        &[CellIndex::Anything, CellIndex::Anything]
    );
    assert_eq!(
        candidate_ids(&definition, &term),
        ["A-first", "B-only", "A-second", "wild"]
    );
    let definition = shape_definition();
    let anywhere = internal_term(
        &definition,
        "top{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortS1{}, SortKItem{}}(h1{}()), dotk{}())))",
    );
    assert_eq!(
        rule_index(&definition, &anywhere).cells(),
        &[CellIndex::Anywhere(Name::from("h1")), CellIndex::Anything]
    );
    assert_eq!(
        subject_index(&definition, &anywhere).cells(),
        &[CellIndex::Anything, CellIndex::Anything]
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
        &[
            CellIndex::Value(KoreString::from(vec![0xff])),
            CellIndex::Anything
        ]
    );
}

#[test]
fn absent_or_unstructured_k_cells_are_wildcards() {
    let definition = definition();
    let absent = internal_term(&definition, "A{}()");
    let malformed = internal_term(&definition, "top{}(Lbl'-LT-'k'-GT-'{}(dotk{}()))");
    assert_eq!(
        rule_index(&definition, &absent).cells(),
        &[CellIndex::Anything, CellIndex::Anything]
    );
    assert_eq!(
        rule_index(&definition, &malformed).cells(),
        &[
            CellIndex::Constructor(Name::from("dotk")),
            CellIndex::Anything
        ]
    );
}

/// A rule `<k> X ~> NEXT ~> R </k>` with a rigid `NEXT`, as a cooling rule is.
fn next_item_rule(label: &str, next: &str) -> String {
    format!(
        r#"axiom{{}} \rewrites{{SortGeneratedTopCell{{}}}}(
            \and{{SortGeneratedTopCell{{}}}}(
              top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(X:SortKItem{{}}, kseq{{}}({next}, R:SortK{{}})))),
              \top{{SortGeneratedTopCell{{}}}}()
            ),
            top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(X:SortKItem{{}}, R:SortK{{}})))
          ) [label{{}}("{label}"), priority{{}}("50")]
        "#
    )
}

fn next_item_definition() -> BackendDefinition {
    definition_with(
        &(next_item_rule("then-A", "A{}()")
            + &next_item_rule("then-B", "B{}()")
            + &next_item_rule("then-f", "f{}()")),
    )
}

#[test]
fn indexes_the_item_after_the_k_sequence_head() {
    let definition = next_item_definition();
    let then_a = |head: &str, next: &str| {
        internal_term(
            &definition,
            &format!(
                "top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, kseq{{}}({next}, dotk{{}}()))))"
            ),
        )
    };
    assert_eq!(
        subject_index(&definition, &then_a("B{}()", "A{}()")).cells(),
        &[
            CellIndex::Constructor(Name::from("B")),
            CellIndex::Constructor(Name::from("A"))
        ]
    );
    assert_eq!(
        candidate_ids(&definition, &then_a("B{}()", "A{}()")),
        ["B-only", "wild", "then-A", "then-f"]
    );
    // A subject-side function in the next position may still evaluate to anything.
    assert_eq!(
        candidate_ids(&definition, &then_a("B{}()", "f{}()")),
        ["B-only", "wild", "then-A", "then-B", "then-f"]
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
    fn every_filtered_rigid_next_item_would_have_failed_matching(
        head_a in any::<bool>(),
        next in prop::sample::select(vec!["A{}()", "B{}()", "f{}()"]),
    ) {
        let definition = next_item_definition();
        let head = if head_a { "A{}()" } else { "B{}()" };
        let subject = internal_term(
            &definition,
            &format!("top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, kseq{{}}({next}, dotk{{}}()))))"),
        );
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

/// `app` (with only `anywhere` equations) overloads the constructor `appv`; `plus` and `v` are in
/// no overload relation.
fn overload_definition() -> BackendDefinition {
    let rule = |label: &str, head: &str| {
        format!(
            r#"axiom{{}} \rewrites{{SortGeneratedTopCell{{}}}}(
                \and{{SortGeneratedTopCell{{}}}}(
                  top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, R:SortK{{}}))),
                  \top{{SortGeneratedTopCell{{}}}}()
                ),
                top{{}}(Lbl'-LT-'k'-GT-'{{}}(R:SortK{{}}))
              ) [label{{}}("{label}"), priority{{}}("50")]
            "#
        )
    };
    let syntax = parse_definition(
        &(r#"[]
        module MAIN
          sort SortK{} []
          sort SortKItem{} []
          sort SortExp{} []
          sort SortVal{} []
          sort SortKCell{} []
          sort SortGeneratedTopCell{} []
          symbol inj{From, To}(From) : To [sortInjection{}()]
          symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), total{}()]
          symbol dotk{}() : SortK{} [constructor{}(), total{}()]
          symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}(), total{}()]
          symbol top{}(SortKCell{}) : SortGeneratedTopCell{} [constructor{}(), total{}()]
          symbol v{}() : SortVal{} [constructor{}(), total{}()]
          symbol appv{}(SortVal{}, SortVal{}) : SortVal{} [constructor{}(), total{}()]
          symbol app{}(SortExp{}, SortExp{}) : SortExp{}
            [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
          symbol plus{}(SortExp{}, SortExp{}) : SortExp{} [constructor{}(), total{}()]
          axiom{R} \exists{R}(
              Value:SortExp{},
              \equals{SortExp{}, R}(Value:SortExp{}, inj{SortVal{}, SortExp{}}(From:SortVal{}))
          ) [subsort{SortVal{}, SortExp{}}()]
          axiom{R} \exists{R}(
              Value:SortKItem{},
              \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortExp{}, SortKItem{}}(From:SortExp{}))
          ) [subsort{SortExp{}, SortKItem{}}()]
          axiom{R} \exists{R}(
              Value:SortKItem{},
              \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortVal{}, SortKItem{}}(From:SortVal{}))
          ) [subsort{SortVal{}, SortKItem{}}()]
          axiom{} \equals{SortExp{}, SortExp{}}(
              app{}(inj{SortVal{}, SortExp{}}(V1:SortVal{}), inj{SortVal{}, SortExp{}}(V2:SortVal{})),
              inj{SortVal{}, SortExp{}}(appv{}(V1:SortVal{}, V2:SortVal{}))
          ) [symbol-overload{}(app{}(), appv{}())]
        "#
        .to_owned()
            + &rule(
                "plus",
                "inj{SortExp{}, SortKItem{}}(plus{}(X:SortExp{}, Y:SortExp{}))",
            )
            + &rule(
                "app",
                "inj{SortExp{}, SortKItem{}}(app{}(X:SortExp{}, Y:SortExp{}))",
            )
            + &rule(
                "appv",
                "inj{SortVal{}, SortKItem{}}(appv{}(X:SortVal{}, Y:SortVal{}))",
            )
            + &rule("v", "inj{SortVal{}, SortKItem{}}(v{}())")
            + "endmodule []"),
    )
    .expect("overload definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("overload definition should internalize")
}

/// Subject heads: a constructor outside every overload, an `app` redex of the overload equation,
/// an `app` no equation rewrites (its first argument is not an injection), a symbolic `app`
/// that the overload equation rewrites for some instances, the overloaded constructor `appv`,
/// and a constant.
const OVERLOAD_SUBJECT_HEADS: [&str; 6] = [
    "inj{SortExp{}, SortKItem{}}(plus{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}())))",
    "inj{SortExp{}, SortKItem{}}(app{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}())))",
    "inj{SortExp{}, SortKItem{}}(app{}(plus{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}())), inj{SortVal{}, SortExp{}}(v{}())))",
    "inj{SortExp{}, SortKItem{}}(app{}(E:SortExp{}, inj{SortVal{}, SortExp{}}(v{}())))",
    "inj{SortVal{}, SortKItem{}}(appv{}(v{}(), v{}()))",
    "inj{SortVal{}, SortKItem{}}(v{}())",
];

#[test]
fn rigid_overloaded_heads_are_keyed_apart_from_heads_outside_every_overload() {
    let definition = overload_definition();
    let app = indexed(&definition, OVERLOAD_SUBJECT_HEADS[2]);
    assert_eq!(
        subject_index(&definition, &app).cells(),
        &[CellIndex::Overloaded, CellIndex::Anything]
    );
    assert_eq!(candidate_ids(&definition, &app), ["app", "appv"]);
    // An `app` application that an equation rewrites, for every instance or only for some, may
    // denote a value with another head, so it keys nothing.
    for head in [OVERLOAD_SUBJECT_HEADS[1], OVERLOAD_SUBJECT_HEADS[3]] {
        let app = indexed(&definition, head);
        assert_eq!(
            subject_index(&definition, &app).cells(),
            &[CellIndex::Anything, CellIndex::Anything]
        );
        assert_eq!(
            candidate_ids(&definition, &app),
            ["plus", "app", "appv", "v"]
        );
    }
    let plus = indexed(&definition, OVERLOAD_SUBJECT_HEADS[0]);
    assert_eq!(candidate_ids(&definition, &plus), ["plus"]);
    assert!(CellIndex::Overloaded.covers(&CellIndex::Anywhere(Name::from("h"))));
    assert!(!CellIndex::Overloaded.covers(&CellIndex::Constructor(Name::from("A"))));
}

proptest! {
    #[test]
    fn every_rule_an_overload_key_filters_would_have_failed_matching(
        head in prop::sample::select(OVERLOAD_SUBJECT_HEADS.to_vec()),
    ) {
        let definition = overload_definition();
        let subject = indexed(&definition, head);
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

/// `<k>` items of every shape the index keys: constructors of a sort, of its supersort and of
/// an unrelated sort, a function, domain values, map and list units, variables (of `KItem` and
/// under an injection), an overloaded constructor and an overloaded `anywhere` production, and
/// `anywhere` productions of two sorts that are in no overload relation, a symbolic `app` that
/// the overload equation rewrites for some instances, and applications of `w1`, whose equation
/// is `w1(s(z)) = w1(z)`: normal and redex, ground and symbolic. The rule side adds conjunctions: an `#as` pattern, two conflicting constructors, and a
/// constructor with a function.
const SHAPE_ITEMS: [&str; 20] = [
    "inj{SortS1{}, SortKItem{}}(a1{}())",
    "inj{SortS1{}, SortKItem{}}(b1{}())",
    "inj{SortS2{}, SortKItem{}}(a2{}())",
    "inj{SortS3{}, SortKItem{}}(a3{}())",
    "inj{SortS1{}, SortKItem{}}(f1{}())",
    r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))"#,
    r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2"))"#,
    "inj{SortMap{}, SortKItem{}}(mapUnit{}())",
    "inj{SortList{}, SortKItem{}}(listUnit{}())",
    "VAR:SortKItem{}",
    "inj{SortS1{}, SortKItem{}}(VARS1:SortS1{})",
    "inj{SortVal{}, SortKItem{}}(appv{}(v{}(), v{}()))",
    "inj{SortExp{}, SortKItem{}}(app{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}())))",
    "inj{SortS1{}, SortKItem{}}(h1{}())",
    "inj{SortS3{}, SortKItem{}}(h3{}())",
    "inj{SortExp{}, SortKItem{}}(app{}(VARE:SortExp{}, inj{SortVal{}, SortExp{}}(v{}())))",
    "inj{SortS1{}, SortKItem{}}(w1{}(z{}()))",
    "inj{SortS1{}, SortKItem{}}(w1{}(s{}(z{}())))",
    "inj{SortS1{}, SortKItem{}}(w1{}(s{}(VARN:SortNat{})))",
    "inj{SortS1{}, SortKItem{}}(w1{}(s{}(s{}(VARN:SortNat{}))))",
];

const SHAPE_RULE_CONJUNCTIONS: [&str; 5] = [
    r"\and{SortKItem{}}(inj{SortS1{}, SortKItem{}}(a1{}()), VARAS:SortKItem{})",
    r"\and{SortKItem{}}(inj{SortS1{}, SortKItem{}}(a1{}()), inj{SortS1{}, SortKItem{}}(b1{}()))",
    r"\and{SortKItem{}}(inj{SortS1{}, SortKItem{}}(a1{}()), inj{SortS1{}, SortKItem{}}(f1{}()))",
    r"\and{SortKItem{}}(inj{SortS1{}, SortKItem{}}(h1{}()), inj{SortS3{}, SortKItem{}}(h3{}()))",
    r"\and{SortKItem{}}(inj{SortS1{}, SortKItem{}}(h1{}()), inj{SortVal{}, SortKItem{}}(appv{}(v{}(), v{}())))",
];

fn shape_definition() -> BackendDefinition {
    let rule = |label: String, contents: String| {
        format!(
            r#"axiom{{}} \rewrites{{SortGeneratedTopCell{{}}}}(
                \and{{SortGeneratedTopCell{{}}}}(
                  top{{}}(Lbl'-LT-'k'-GT-'{{}}({contents})),
                  \top{{SortGeneratedTopCell{{}}}}()
                ),
                top{{}}(Lbl'-LT-'k'-GT-'{{}}(dotk{{}}()))
              ) [label{{}}("{label}"), priority{{}}("50")]
            "#
        )
    };
    let mut rules = String::new();
    for (position, item) in SHAPE_ITEMS
        .iter()
        .chain(&SHAPE_RULE_CONJUNCTIONS)
        .enumerate()
    {
        let item = item.replace("VAR", "RULEVAR");
        rules += &rule(
            format!("head-{position}"),
            format!("kseq{{}}({item}, REST:SortK{{}})"),
        );
        rules += &rule(
            format!("next-{position}"),
            format!("kseq{{}}(FIRST:SortKItem{{}}, kseq{{}}({item}, REST:SortK{{}}))"),
        );
    }
    let subsort = |sub: &str, sup: &str| {
        format!(
            r"axiom{{R}} \exists{{R}}(
                Value:Sort{sup}{{}},
                \equals{{Sort{sup}{{}}, R}}(Value:Sort{sup}{{}}, inj{{Sort{sub}{{}}, Sort{sup}{{}}}}(From:Sort{sub}{{}}))
            ) [subsort{{Sort{sub}{{}}, Sort{sup}{{}}}}()]
            "
        )
    };
    let subsorts = [
        ("S1", "S2"),
        ("S1", "KItem"),
        ("S2", "KItem"),
        ("S3", "KItem"),
        ("Int", "KItem"),
        ("Map", "KItem"),
        ("List", "KItem"),
        ("Val", "Exp"),
        ("Val", "KItem"),
        ("Exp", "KItem"),
    ]
    .iter()
    .map(|(sub, sup)| subsort(sub, sup))
    .collect::<String>();
    let syntax = parse_definition(
        &(r#"[]
        module MAIN
          sort SortK{} []
          sort SortKItem{} []
          sort SortKCell{} []
          sort SortGeneratedTopCell{} []
          sort SortS1{} []
          sort SortS2{} []
          sort SortS3{} []
          sort SortVal{} []
          sort SortExp{} []
          sort SortNat{} []
          sort SortInt{} [hasDomainValues{}()]
          hooked-sort SortMap{}
            [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
          hooked-sort SortList{}
            [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
          symbol inj{From, To}(From) : To [sortInjection{}()]
          symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), total{}()]
          symbol dotk{}() : SortK{} [constructor{}(), total{}()]
          symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}(), total{}()]
          symbol top{}(SortKCell{}) : SortGeneratedTopCell{} [constructor{}(), total{}()]
          symbol a1{}() : SortS1{} [constructor{}(), total{}()]
          symbol b1{}() : SortS1{} [constructor{}(), total{}()]
          symbol a2{}() : SortS2{} [constructor{}(), total{}()]
          symbol a3{}() : SortS3{} [constructor{}(), total{}()]
          symbol f1{}() : SortS1{} [function{}(), total{}()]
          symbol h1{}() : SortS1{} [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
          symbol h3{}() : SortS3{} [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
          symbol z{}() : SortNat{} [constructor{}(), total{}()]
          symbol s{}(SortNat{}) : SortNat{} [constructor{}(), total{}()]
          symbol w1{}(SortNat{}) : SortS1{} [anywhere{}(), functional{}(), injective{}()]
          axiom{R} \implies{R}(
              \and{R}(
                  \top{R}(),
                  \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
              ),
              \equals{SortS1{}, R}(
                  w1{}(X0:SortNat{}),
                  \and{SortS1{}}(w1{}(z{}()), \top{SortS1{}}())
              )
          ) [anywhere{}()]
          symbol v{}() : SortVal{} [constructor{}(), total{}()]
          symbol appv{}(SortVal{}, SortVal{}) : SortVal{} [constructor{}(), total{}()]
          symbol app{}(SortExp{}, SortExp{}) : SortExp{}
            [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
          hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
          hooked-symbol mapItem{}(SortKItem{}, SortKItem{}) : SortMap{}
            [function{}(), total{}(), hook{}("MAP.element")]
          hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
            [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
          hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
          hooked-symbol listItem{}(SortKItem{}) : SortList{}
            [function{}(), total{}(), hook{}("LIST.element")]
          hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
            [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
          axiom{} \equals{SortExp{}, SortExp{}}(
              app{}(inj{SortVal{}, SortExp{}}(V1:SortVal{}), inj{SortVal{}, SortExp{}}(V2:SortVal{})),
              inj{SortVal{}, SortExp{}}(appv{}(V1:SortVal{}, V2:SortVal{}))
          ) [symbol-overload{}(app{}(), appv{}())]
        "#
        .to_owned()
            + &subsorts
            + &rules
            + "endmodule []"),
    )
    .expect("shape definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("shape definition should internalize")
}

/// Every rule the index drops for a subject fails to match it, over every pair of item shapes
/// at the `<k>` head and after it, on both sides.
#[test]
fn every_rule_the_index_drops_fails_to_match_for_every_item_shape() {
    let definition = shape_definition();
    let mut dropped = 0;
    for head in SHAPE_ITEMS {
        for next in SHAPE_ITEMS {
            let head = head.replace("VAR", "SUBJECTHEAD");
            let next = next.replace("VAR", "SUBJECTNEXT");
            let subject = internal_term(
                &definition,
                &format!(
                    "top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, kseq{{}}({next}, dotk{{}}()))))"
                ),
            );
            let subject_index = subject_index(&definition, &subject);
            for stored in old_candidates(&definition, &term_index(&subject)) {
                if stored.index.covers(&subject_index) {
                    continue;
                }
                dropped += 1;
                let result = match_terms_in_definition(
                    MatchMode::Rewrite,
                    &definition,
                    &stored.lhs,
                    &subject,
                );
                assert!(
                    matches!(result, MatchResult::Failed(_)),
                    "{} dropped for <k> {head} ~> {next}, but matching gives {result:?}",
                    stored.attributes.label.as_deref().unwrap_or("?"),
                );
            }
        }
    }
    // The index drops something for most subjects; a vacuous pass would drop nothing.
    assert!(dropped > 1000, "only {dropped} dropped candidates");
}
