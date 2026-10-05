//! Constructor schemas build values only at free instance sorts, including after alias expansion.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::{BackendDefinition, ConstructorHead, DefinitionError},
    rewrite::violates_finite_constructor_domain,
    rule::Predicate,
    term::{Sort, Term, Variable},
    verify::SentenceContext,
};

const COMPLETE_NO_JUNK: &str = r#"
    axiom{} \or{SortFoo{}}(
        g{}(),
        \exists{SortFoo{}}(X0:SortFoo{}, wrap{SortFoo{}}(X0:SortFoo{})),
        \bottom{SortFoo{}}()
    ) [constructor{}()]
"#;

fn source(sentences: &str) -> String {
    format!(
        r#"[]
        module MAIN
            sort SortFoo{{}} []
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            sort SortLiteral{{}} [hasDomainValues{{}}()]
            hooked-sort SortHooked{{}} [hook{{}}("MAP.Map")]
            symbol g{{}}() : SortFoo{{}} [constructor{{}}()]
            symbol wrap{{S}}(S) : S [constructor{{}}(), functional{{}}(), injective{{}}()]
            {sentences}
        endmodule []"#
    )
}

fn internalize(sentences: &str) -> Result<BackendDefinition, DefinitionError> {
    let syntax = parse_definition(&source(sentences)).expect("schema definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
}

#[test]
fn complete_schema_domain_keeps_the_non_g_branch_feasible() {
    let definition = internalize(COMPLETE_NO_JUNK).expect("constructor schema should load");
    let foo = Sort::simple("SortFoo");
    let expected = BTreeSet::from([
        ConstructorHead::Symbol {
            name: "g".into(),
            sort_arguments: vec![],
        },
        ConstructorHead::Symbol {
            name: "wrap".into(),
            sort_arguments: vec![foo.clone()],
        },
    ]);
    let domain = definition
        .finite_constructor_heads(&foo)
        .expect("the axiom lists every constructor instance");
    assert!(expected.iter().all(|head| domain.contains(head)));
    assert!(domain.is_covered_by(&expected));

    let pattern = parse_pattern("g{}()").unwrap();
    let g = definition
        .verify_standalone_pattern(&pattern, &[])
        .unwrap()
        .internalize_term()
        .unwrap();
    let x = Term::variable(Variable::new("X", foo));
    assert!(!violates_finite_constructor_domain(
        &definition,
        &[Predicate::Not(Box::new(Predicate::Equals(x, g)))],
    ));
}

#[test]
fn omitted_schema_instance_prevents_a_finite_domain() {
    let definition =
        internalize(r#"axiom{} \or{SortFoo{}}(g{}(), \bottom{SortFoo{}}()) [constructor{}()]"#)
            .expect("an incomplete no-junk axiom still loads");
    assert!(
        definition
            .finite_constructor_heads(&Sort::simple("SortFoo"))
            .is_none()
    );
}

#[test]
fn schema_instances_at_fixed_sorts_are_rejected_in_sentences() {
    for (sentence, context) in [
        (
            r#"axiom{} wrap{SortInt{}}(\dv{SortInt{}}("1")) []"#,
            SentenceContext::Axiom { index: 0 },
        ),
        (
            r#"claim{} wrap{SortInt{}}(\dv{SortInt{}}("1")) []"#,
            SentenceContext::Claim { index: 0 },
        ),
        (
            r#"alias bad{}(SortInt{}) : SortInt{}
                where bad{}(X:SortInt{}) := wrap{SortInt{}}(X:SortInt{}) []"#,
            SentenceContext::Alias("bad".into()),
        ),
    ] {
        let Err(DefinitionError::Verification(error)) = internalize(sentence) else {
            panic!("a schema instance at Int must be refused: {sentence}");
        };
        assert_eq!(error.sentence, context);
        assert!(
            error
                .message
                .contains("Constructor wrap is applied at sort SortInt{}"),
            "{error}"
        );
    }
}

#[test]
fn standalone_schema_instances_require_a_free_sort() {
    let definition = internalize(COMPLETE_NO_JUNK).expect("constructor schema should load");
    for (sort, operand) in [
        ("SortInt", r#"\dv{SortInt{}}("1")"#),
        ("SortLiteral", r#"\dv{SortLiteral{}}("x")"#),
        ("SortHooked", "X:SortHooked{}"),
    ] {
        let pattern = parse_pattern(&format!("wrap{{{sort}{{}}}}({operand})")).unwrap();
        let Err(DefinitionError::Verification(error)) =
            definition.verify_standalone_pattern(&pattern, &[])
        else {
            panic!("a schema instance at {sort} must be refused");
        };
        assert_eq!(error.sentence, SentenceContext::Standalone);
        assert!(
            error
                .message
                .contains(&format!("is applied at sort {sort}{{}}")),
            "{error}"
        );
    }
    let pattern = parse_pattern("wrap{SortFoo{}}(g{}())").unwrap();
    assert!(definition.verify_standalone_pattern(&pattern, &[]).is_ok());
}

#[test]
fn schema_instances_at_sentence_sort_variables_are_accepted() {
    internalize(
        r#"axiom{S} \exists{S}(V:S, \equals{S, S}(V:S, wrap{S}(X:S))) [functional{}()]
           alias generic{S}(S) : S where generic{S}(X:S) := wrap{S}(X:S) []"#,
    )
    .expect("schema axioms and aliases may retain their bound sort variable");
}

#[test]
fn associative_schema_instances_are_checked_before_folding() {
    let definition =
        internalize("symbol merge{S}(S, S) : S [constructor{}(), functional{}(), injective{}()]")
            .expect("binary constructor schema should load");
    for direction in ["left", "right"] {
        let pattern = parse_pattern(&format!(
            r#"\{direction}-assoc{{}}(merge{{SortInt{{}}}}(\dv{{SortInt{{}}}}("1"), \dv{{SortInt{{}}}}("2")))"#,
        ))
        .unwrap();
        let Err(DefinitionError::Verification(error)) =
            definition.verify_standalone_pattern(&pattern, &[])
        else {
            panic!("an associative schema instance at Int must be refused");
        };
        assert!(
            error
                .message
                .contains("Constructor merge is applied at sort SortInt{}")
        );
        let pattern = parse_pattern(&format!(
            r#"\{direction}-assoc{{}}(merge{{SortFoo{{}}}}(g{{}}(), g{{}}()))"#,
        ))
        .unwrap();
        assert!(definition.verify_standalone_pattern(&pattern, &[]).is_ok());
    }
}

#[test]
fn alias_instantiation_must_not_admit_a_fixed_sort_constructor() {
    let definition =
        internalize("alias generic{S}(S) : S where generic{S}(X:S) := wrap{S}(X:S) []")
            .expect("generic alias definition should load");
    let direct = parse_pattern(r#"wrap{SortInt{}}(\dv{SortInt{}}("1"))"#).unwrap();
    assert!(definition.verify_standalone_pattern(&direct, &[]).is_err());
    let aliased = parse_pattern(r#"generic{SortInt{}}(\dv{SortInt{}}("1"))"#).unwrap();
    let error = definition
        .verify_standalone_pattern(&aliased, &[])
        .unwrap()
        .internalize_term()
        .expect_err("alias expansion must reject the fixed-sort constructor instance");
    assert!(
        error
            .to_string()
            .contains("Constructor wrap is applied at sort SortInt{}"),
        "{error}"
    );
    let free = parse_pattern("generic{SortFoo{}}(g{}())").unwrap();
    let term = definition
        .verify_standalone_pattern(&free, &[])
        .unwrap()
        .internalize_term()
        .unwrap();
    let crate::term::TermKind::Application {
        symbol,
        sort_arguments,
        ..
    } = term.kind()
    else {
        panic!("free-sort alias should expand to the constructor");
    };
    assert_eq!(symbol.name.as_ref(), "wrap");
    assert_eq!(sort_arguments, &[Sort::simple("SortFoo")]);
}

#[test]
fn internalization_enforces_schema_instances_without_verification() {
    let definition = internalize("").unwrap();
    for sort in ["SortInt", "SortLiteral", "SortHooked"] {
        let pattern = parse_pattern(&format!("wrap{{{sort}{{}}}}(X:{sort}{{}})")).unwrap();
        for error in [
            definition
                .admit_unverified(&pattern, &[])
                .internalize_term()
                .unwrap_err(),
            definition.internalize_term(&pattern, &[]).unwrap_err(),
        ] {
            assert!(
                error
                    .to_string()
                    .contains(&format!("Constructor wrap is applied at sort {sort}{{}}")),
                "{error}"
            );
        }
    }
    let free = parse_pattern("wrap{SortFoo{}}(g{}())").unwrap();
    assert!(
        definition
            .admit_unverified(&free, &[])
            .internalize_term()
            .is_ok()
    );
    let generic = parse_pattern("wrap{S}(X:S)").unwrap();
    assert!(
        definition
            .verify_standalone_pattern(&generic, &["S".into()])
            .unwrap()
            .internalize_term()
            .is_ok()
    );
}

#[test]
fn alias_instances_at_fixed_sorts_are_rejected_in_executable_sentences() {
    for sentence in [
        r#"axiom{} \rewrites{SortInt{}}(
               \and{SortInt{}}(\top{SortInt{}}(), generic{SortInt{}}(X:SortInt{})),
               X:SortInt{}
           ) []"#,
        r#"alias weakExistsFinally{S}(S) : S
               where weakExistsFinally{S}(@X:S) := @X:S []
           claim{} \implies{SortInt{}}(
               \and{SortInt{}}(\top{SortInt{}}(), generic{SortInt{}}(X:SortInt{})),
               weakExistsFinally{SortInt{}}(X:SortInt{})
           ) []"#,
    ] {
        let error = internalize(&format!(
            "alias generic{{S}}(S) : S where generic{{S}}(X:S) := wrap{{S}}(X:S) []\n{sentence}"
        ))
        .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("Constructor wrap is applied at sort SortInt{}"),
            "{error}"
        );
    }
}

#[test]
fn sort_injections_into_hooked_sorts_preserve_subsort_values() {
    let sentences = r#"
        symbol inj{From, To}(From) : To [sortInjection{}()]
        axiom{R} \exists{R}(Val:SortHooked{},
            \equals{SortHooked{}, R}(Val:SortHooked{},
                inj{SortFoo{}, SortHooked{}}(From:SortFoo{})))
            [subsort{SortFoo{}, SortHooked{}}()]
    "#;
    let syntax = parse_definition(&source(sentences)).unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("a hooked sort without domain values may contain a subsort's values");
    crate::verify::verify_definition(
        &[&syntax.modules[0]],
        &syntax.modules,
        definition.sorts(),
        definition.symbols(),
        &Default::default(),
        &crate::nesting::Syntactic,
    )
    .expect("the subsort axiom's injection must verify");
    let pattern = parse_pattern("inj{SortFoo{}, SortHooked{}}(g{}())").unwrap();
    let verified = definition
        .verify_standalone_pattern(&pattern, &[])
        .unwrap()
        .internalize_term()
        .unwrap();
    assert_eq!(verified.sort(), Sort::simple("SortHooked"));
    assert_eq!(
        definition
            .admit_unverified(&pattern, &[])
            .internalize_term()
            .unwrap(),
        verified,
    );
    assert_eq!(
        definition.internalize_term(&pattern, &[]).unwrap(),
        verified
    );
}

#[test]
fn constructor_attribute_requires_a_free_instance_sort_even_with_sort_injection() {
    let definition = internalize(
        "symbol both{S}(S) : S [constructor{}(), sortInjection{}(), functional{}(), injective{}()]",
    )
    .expect("constructor schema carrying sortInjection should load");
    let pattern = parse_pattern(r#"both{SortInt{}}(\dv{SortInt{}}("1"))"#).unwrap();
    for error in [
        definition
            .verify_standalone_pattern(&pattern, &[])
            .err()
            .expect("a declared constructor at Int must fail verification"),
        definition
            .admit_unverified(&pattern, &[])
            .internalize_term()
            .unwrap_err(),
    ] {
        assert!(
            error
                .to_string()
                .contains("Constructor both is applied at sort SortInt{}"),
            "{error}"
        );
    }
}

#[test]
fn sort_injection_attribute_is_distinct_from_constructor_regardless_of_name() {
    // This tests only that the schema check ignores a sortInjection-only declaration,
    // whatever its name; subsort validation is a separate condition on `inj` applications.
    let definition = internalize(
        r#"symbol embed{From, To}(From) : To [sortInjection{}()]
           axiom{R} \exists{R}(Val:SortHooked{},
               \equals{SortHooked{}, R}(Val:SortHooked{},
                   embed{SortFoo{}, SortHooked{}}(g{}()))) [functional{}()]"#,
    )
    .expect("the instance check applies only to declarations carrying constructor");
    let pattern = parse_pattern("embed{SortFoo{}, SortHooked{}}(g{}())").unwrap();
    let verified = definition
        .verify_standalone_pattern(&pattern, &[])
        .unwrap()
        .internalize_term()
        .unwrap();
    assert_eq!(
        definition
            .admit_unverified(&pattern, &[])
            .internalize_term()
            .unwrap(),
        verified,
    );
    assert_eq!(
        definition.internalize_term(&pattern, &[]).unwrap(),
        verified
    );
}
