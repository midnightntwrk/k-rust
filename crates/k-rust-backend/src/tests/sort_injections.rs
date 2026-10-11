//! Loaded injections are licensed embeddings; impossible matched patterns denote no value.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::{BackendDefinition, DefinitionError, UnlicensedInjectionSite},
    rule::{Predicate, TermIndex, internalize_predicate},
    simplify::{SimplificationOptions, simplify},
    term::{Name, Sort, Term},
};

fn load(source: &str) -> Result<BackendDefinition, DefinitionError> {
    BackendDefinition::internalize(
        &parse_definition(source).expect("definition should parse"),
        "TEST",
    )
}

fn source(axioms: &str) -> String {
    format!(
        r#"[] module TEST
            sort SortA{{}} []
            sort SortB{{}} []
            symbol a{{}}() : SortA{{}} [constructor{{}}(), total{{}}()]
            symbol b{{}}() : SortB{{}} [constructor{{}}(), total{{}}()]
            symbol f{{}}() : SortB{{}} [function{{}}(), total{{}}()]
            symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
            alias weakExistsFinally{{S}}(S) : S
                where weakExistsFinally{{S}}(@X:S) := @X:S []
            {axioms}
        endmodule []"#,
    )
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).unwrap(), &[])
        .expect("licensed term should internalize")
}

fn assert_written_refused(axiom: &str, identity: &str) {
    let error = load(&source(axiom)).expect_err("written unlicensed injection must be refused");
    let debug = format!("{error:?}");
    assert!(debug.contains("UnlicensedInjection"), "{debug}");
    for expected in ["SortA", "SortB", identity] {
        assert!(error.to_string().contains(expected), "{error}");
    }
}

#[test]
fn function_written_injection_is_refused_naming_the_label_over_the_unique_id() {
    let axiom = r#"axiom{R} \implies{R}(\and{R}(\top{R}(), \top{R}()),
            \equals{SortB{},R}(f{}(), \and{SortB{}}(
                inj{SortA{},SortB{}}(a{}()), \top{SortB{}}())))
            [UNIQUE'Unds'ID{}("a1b2c3"), label{}("written-function")]"#;
    assert_written_refused(axiom, "written-function");
    let error = load(&source(axiom)).expect_err("written unlicensed injection must be refused");
    assert!(!error.to_string().contains("a1b2c3"), "{error}");
}

#[test]
fn rewrite_written_injection_is_refused_with_axiom_label() {
    assert_written_refused(
        r#"axiom{} \rewrites{SortB{}}(
            \and{SortB{}}(b{}(), \top{SortB{}}()),
            inj{SortA{},SortB{}}(a{}())) [label{}("written-rewrite")]"#,
        "written-rewrite",
    );
}

#[test]
fn written_injection_with_unknown_unique_id_uses_label() {
    let error = load(&source(
        r#"axiom{} \rewrites{SortB{}}(
            \and{SortB{}}(b{}(), \top{SortB{}}()),
            inj{SortA{},SortB{}}(a{}())) [UNIQUE'Unds'ID{}("UNKNOWN"), label{}("fallback-label")]"#,
    ))
    .expect_err("written unlicensed injection must be refused");
    assert_eq!(
        error.to_string(),
        "Unlicensed injection from SortA{} to SortB{} in axiom fallback-label",
    );
}

#[test]
fn written_injection_without_identity_names_its_position() {
    for (attributes, expected) in [
        (
            r#"org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(fixture.k)"), org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(3,1,7,2)")"#,
            "at fixture.k:3:1",
        ),
        (
            r#"org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(3,1,7,2)")"#,
            "at 3:1",
        ),
        (
            r#"org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(fixture.k)")"#,
            "at fixture.k",
        ),
    ] {
        let error = load(&source(&format!(
            r"axiom{{}} \rewrites{{SortB{{}}}}(\and{{SortB{{}}}}(b{{}}(), \top{{SortB{{}}}}()),
                inj{{SortA{{}},SortB{{}}}}(a{{}}())) [{attributes}]",
        )))
        .expect_err("written unlicensed injection must be refused");
        assert_eq!(
            error.to_string(),
            format!("Unlicensed injection from SortA{{}} to SortB{{}} in axiom {expected}"),
        );
    }
}

#[test]
fn written_injection_without_identity_reports_module_and_sentence() {
    let error = load(&source(
        r"axiom{} \rewrites{SortB{}}(\and{SortB{}}(b{}(), \top{SortB{}}()),
            inj{SortA{},SortB{}}(a{}())) []",
    ))
    .expect_err("written unlicensed injection must be refused");
    assert_eq!(
        error.to_string(),
        "Unlicensed injection from SortA{} to SortB{} in axiom at sentence index 7 (zero-based) of module TEST",
    );
}

#[test]
fn claim_written_injection_is_refused() {
    let error = load(&source(
        r#"claim{} \implies{SortB{}}(
            \and{SortB{}}(b{}(), \top{SortB{}}()),
            weakExistsFinally{SortB{}}(inj{SortA{},SortB{}}(a{}()))) []"#,
    ))
    .expect_err("a claim may not write an unlicensed injection");
    assert_eq!(
        error,
        DefinitionError::NotSubsort {
            source: Box::new(crate::externalize::sort(&Sort::simple("SortA"))),
            target: Box::new(crate::externalize::sort(&Sort::simple("SortB"))),
        },
    );
}

const DEAD_BINDER: &str = r#"[]
module TEST
  sort SortK{} []
  sort SortKItem{} []
  sort SortA{} []
  sort SortL{} [hasDomainValues{}()]
  hooked-sort SortBool{} [hasDomainValues{}(), hook{}("BOOL.Bool")]
  symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
  symbol dotk{}() : SortK{} [constructor{}(), functional{}(), injective{}()]
  symbol a{}() : SortA{} [constructor{}(), functional{}()]
  symbol inj{From, To}(From) : To [sortInjection{}()]
  symbol isL{}(SortK{}) : SortBool{} [function{}(), total{}()]
  axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{}, R}(Val:SortKItem{}, inj{SortA{}, SortKItem{}}(From:SortA{}))) [subsort{SortA{}, SortKItem{}}()]
  axiom{R} \implies{R}(
    \and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, kseq{}(inj{SortL{}, SortKItem{}}(V:SortL{}), dotk{}())), \top{R}())),
    \equals{SortBool{}, R}(isL{}(X0:SortK{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
  axiom{R} \implies{R}(
    \and{R}(
      \not{R}(\or{R}(\exists{R}(V:SortL{}, \and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, kseq{}(inj{SortL{}, SortKItem{}}(V:SortL{}), dotk{}())), \top{R}()))), \bottom{R}())),
      \and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, K:SortK{}), \top{R}()))),
    \equals{SortBool{}, R}(isL{}(X0:SortK{}), \and{SortBool{}}(\dv{SortBool{}}("false"), \top{SortBool{}}()))) [owise{}()]
endmodule []
"#;

#[test]
fn dead_function_binder_is_absent_from_theory() {
    let definition = load(DEAD_BINDER).expect("dead binder definition should load");
    let equations = &definition.function_theory()[&TermIndex::Symbol(Name::from("isL"))];
    assert_eq!(equations.values().map(Vec::len).sum::<usize>(), 1);
    assert!(
        equations
            .values()
            .flatten()
            .all(|rule| rule.attributes.priority == u8::MAX)
    );
}

#[test]
fn dead_membership_is_false_only_inside_axioms() {
    let definition = load(DEAD_BINDER).expect("dead binder definition should load");
    let membership = parse_pattern(
        r"\in{SortK{}, SortBool{}}(X:SortK{}, kseq{}(inj{SortL{}, SortKItem{}}(V:SortL{}), dotk{}()))",
    )
    .unwrap();
    assert_eq!(
        internalize_predicate(
            &definition,
            &membership,
            &[],
            UnlicensedInjectionSite::InAxiom
        )
        .expect("an impossible axiom membership denotes false"),
        Predicate::False,
    );
    assert_eq!(
        internalize_predicate(
            &definition,
            &membership,
            &[],
            UnlicensedInjectionSite::Refuse
        ),
        Err(DefinitionError::NotSubsort {
            source: Box::new(crate::externalize::sort(&Sort::simple("SortL"))),
            target: Box::new(crate::externalize::sort(&Sort::simple("SortKItem"))),
        }),
    );
}

#[test]
fn unlicensed_membership_in_predicate_lhs_makes_axiom_dead() {
    let definition = load(
        r#"[]
module TEST
  sort SortA{} []
  sort SortB{} []
  symbol a{}() : SortA{} [constructor{}(), total{}(), functional{}()]
  symbol b{}() : SortB{} [constructor{}(), total{}(), functional{}()]
  symbol c{}() : SortB{} [constructor{}(), total{}(), functional{}()]
  symbol g{}(SortB{}) : SortB{} [function{}(), total{}()]
  symbol inj{S,T}(S) : T [sortInjection{}()]
  axiom{R} \implies{R}(\top{R}(),
    \equals{R,R}(\in{SortB{},R}(X:SortB{}, inj{SortA{},SortB{}}(Y:SortA{})),
      \and{R}(\bottom{R}(), \top{R}()))) [simplification{}(), UNIQUE'Unds'ID{}("junk-membership-lemma")]
  axiom{R} \implies{R}(\and{R}(\equals{SortB{},R}(X0:SortB{}, b{}()), \and{R}(\in{SortB{},R}(X1:SortB{}, X0:SortB{}), \top{R}())),
    \equals{SortB{},R}(g{}(X1:SortB{}), \and{SortB{}}(c{}(), \top{SortB{}}()))) [UNIQUE'Unds'ID{}("g-b")]
endmodule []"#,
    )
    .expect("dead predicate simplification should not prevent loading");
    assert!(definition.predicate_simplification_theory().is_empty());
    let input = term(&definition, "g{}(c{}())");
    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("refuted function condition should simplify without recursion")
        .expect("the stuck function application is not bottom");
    assert_eq!(result.term, input);
    assert!(result.constraints().is_empty());

    let membership =
        parse_pattern(r"\in{SortB{},R}(X:SortB{}, inj{SortA{},SortB{}}(Y:SortA{}))").unwrap();
    assert_eq!(
        internalize_predicate(
            &definition,
            &membership,
            &[Name::from("R")],
            UnlicensedInjectionSite::InAxiomMatched,
        ),
        Err(DefinitionError::NotSubsort {
            source: Box::new(crate::externalize::sort(&Sort::simple("SortA"))),
            target: Box::new(crate::externalize::sort(&Sort::simple("SortB"))),
        }),
    );

    let schema = parse_pattern(r"\in{T,R}(X:T, inj{S,T}(Y:S))").unwrap();
    assert!(matches!(
        internalize_predicate(
            &definition,
            &schema,
            &[Name::from("S"), Name::from("T"), Name::from("R")],
            UnlicensedInjectionSite::InAxiomMatched,
        ),
        Ok(Predicate::In(_, _)),
    ));
}

#[test]
fn dead_binder_controls_decide_licensed_and_symbolic_values_as_false() {
    let definition = load(DEAD_BINDER).expect("dead binder definition should load");
    for (input, expected) in [
        (
            "isL{}(kseq{}(inj{SortA{}, SortKItem{}}(a{}()), dotk{}()))",
            r#"\dv{SortBool{}}("false")"#,
        ),
        ("isL{}(K:SortK{})", r#"\dv{SortBool{}}("false")"#),
    ] {
        let result = simplify(
            &definition,
            &term(&definition, input),
            SimplificationOptions::default(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(result.term, term(&definition, expected));
        assert!(result.constraints().is_empty());
    }
}

#[test]
fn licensed_definition_loads_and_round_trips() {
    let definition = load(&source(
        r#"axiom{R} \exists{R}(Val:SortB{}, \equals{SortB{}, R}(
                Val:SortB{}, inj{SortA{}, SortB{}}(From:SortA{})))
                [subsort{SortA{}, SortB{}}()]
           axiom{R} \implies{R}(\and{R}(\top{R}(), \top{R}()),
                \equals{SortB{}, R}(f{}(), \and{SortB{}}(
                    inj{SortA{}, SortB{}}(a{}()), \top{SortB{}}()))) []"#,
    ))
    .expect("licensed function equation should load");
    let expected = term(&definition, "inj{SortA{}, SortB{}}(a{}())");
    let result = simplify(
        &definition,
        &term(&definition, "f{}()"),
        SimplificationOptions::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(result.term, expected);
    let external = crate::externalize::term(&result.term).to_string();
    assert_eq!(term(&definition, &external), expected);
}

#[test]
fn injection_composition_schema_loads() {
    load(&source(
        r#"axiom{S1,S2,S3} \equals{S3,S3}(
            inj{S2,S3}(inj{S1,S2}(T:S1)), inj{S1,S3}(T:S1))
            [simplification{}()]"#,
    ))
    .expect("sort-variable injection composition is a licensed schema");
    let definition = load(&source(
        r#"axiom{S1,S2,S3,R} \implies{R}(\top{R}(),
            \equals{S3,R}(inj{S2,S3}(inj{S1,S2}(T:S1)),
                \and{S3}(inj{S1,S3}(T:S1), \top{S3}())))
            [simplification{}()]"#,
    ))
    .expect("an executable injection-composition schema is licensed while open");
    assert!(!definition.simplification_theory().is_empty());
}

#[test]
fn rewrite_keeps_original_live_alternative_index() {
    let definition = load(&source(
        r#"axiom{} \rewrites{SortB{}}(
            \and{SortB{}}(\or{SortB{}}(
                inj{SortA{}, SortB{}}(X:SortA{}), b{}()),
                \top{SortB{}}()), b{}()) []"#,
    ))
    .expect("licensed rewrite alternative should remain live");
    let rules = definition
        .rewrite_theory()
        .values()
        .flat_map(|groups| groups.values())
        .flatten()
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].lhs, term(&definition, "b{}()"));
    assert_eq!(rules[0].lhs_alternative, Some(1));
}

#[test]
fn dead_simplification_and_ceil_patterns_do_not_read_written_positions() {
    for axiom in [
        r#"axiom{R} \implies{R}(\top{R}(),
            \equals{SortB{},R}(inj{SortA{},SortB{}}(X:SortA{}),
                \and{SortB{}}(inj{SortA{},SortB{}}(a{}()), \top{SortB{}}())))
            [simplification{}()]"#,
        r#"axiom{R} \implies{R}(\top{R}(),
            \equals{R,R}(\equals{SortB{},R}(
                inj{SortA{},SortB{}}(X:SortA{}), b{}()),
                \and{R}(\equals{SortB{},R}(inj{SortA{},SortB{}}(a{}()), b{}()), \top{R}())))
            [simplification{}()]"#,
        r#"axiom{R} \implies{R}(\top{R}(),
            \equals{R,R}(\ceil{SortB{},R}(inj{SortA{},SortB{}}(X:SortA{})),
                \and{R}(\equals{SortB{},R}(inj{SortA{},SortB{}}(a{}()), b{}()), \top{R}()))) []"#,
    ] {
        let definition = load(&source(axiom)).expect("dead matched pattern should drop its axiom");
        assert!(definition.simplification_theory().is_empty());
        assert!(definition.predicate_simplification_theory().is_empty());
        assert!(definition.ceil_theory().is_empty());
    }
}

#[test]
fn written_requires_and_ensures_are_refused() {
    for axiom in [
        r#"axiom{} \rewrites{SortB{}}(
            \and{SortB{}}(b{}(), \equals{SortB{},SortB{}}(
                inj{SortA{},SortB{}}(a{}()), b{}())), b{}())
            [label{}("written-condition")]"#,
        r#"axiom{R} \implies{R}(
            \and{R}(\equals{SortB{},R}(inj{SortA{},SortB{}}(a{}()), b{}()), \top{R}()),
            \equals{SortB{},R}(f{}(), \and{SortB{}}(b{}(), \top{SortB{}}())))
            [label{}("written-condition")]"#,
        r#"axiom{R} \implies{R}(\and{R}(\top{R}(), \top{R}()),
            \equals{SortB{},R}(f{}(), \and{SortB{}}(b{}(),
                \equals{SortB{},SortB{}}(inj{SortA{},SortB{}}(a{}()), b{}()))))
            [label{}("written-condition")]"#,
        r#"axiom{} \rewrites{SortB{}}(
            \and{SortB{}}(b{}(), \top{SortB{}}()),
            \and{SortB{}}(b{}(), \equals{SortB{},SortB{}}(
                inj{SortA{},SortB{}}(a{}()), b{}()))) [label{}("written-condition")]"#,
    ] {
        assert_written_refused(axiom, "written-condition");
    }
}

#[test]
fn no_junk_with_unlicensed_alternative_has_no_finite_domain() {
    let definition = load(&source(
        r#"axiom{} \or{SortB{}}(b{}(),
            \exists{SortB{}}(X:SortA{}, inj{SortA{},SortB{}}(X:SortA{})),
            \bottom{SortB{}}()) [constructor{}()]"#,
    ))
    .expect("an invalid no-junk alternative should conservatively suppress the finite domain");
    assert!(
        definition
            .finite_constructor_heads(&Sort::simple("SortB"))
            .is_none()
    );
}

/// Internalization is the step every admission route shares, so whether a pattern is
/// well-sorted cannot depend on the route: a pattern the verifier refuses for a sort reason is
/// refused by internalization too. `inj{S, T}(t)` is an application whose argument sort is `S`,
/// so an operand of another sort, a strict subsort of `S` included, is refused; the ordinary
/// symbol is the control.
#[test]
fn internalization_refuses_what_the_verifier_refuses_for_its_sorts() {
    let definition = load(
        r#"[] module TEST
            sort SortKItem{} []
            sort SortFoo{} []
            sort SortSub{} []
            sort SortS{} []
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol inj{From, To}(From) : To [sortInjection{}()]
            axiom{R} \exists{R}(Value:SortKItem{},
                \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortFoo{}, SortKItem{}}(From:SortFoo{})))
                [subsort{SortFoo{}, SortKItem{}}()]
            axiom{R} \exists{R}(Value:SortKItem{},
                \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
                [subsort{SortInt{}, SortKItem{}}()]
            axiom{R} \exists{R}(Value:SortFoo{},
                \equals{SortFoo{}, R}(Value:SortFoo{}, inj{SortSub{}, SortFoo{}}(From:SortSub{})))
                [subsort{SortSub{}, SortFoo{}}()]
            axiom{R} \exists{R}(Value:SortKItem{},
                \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortSub{}, SortKItem{}}(From:SortSub{})))
                [subsort{SortSub{}, SortKItem{}}()]
            symbol c{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
            symbol s{}() : SortSub{} [constructor{}(), functional{}(), injective{}()]
            symbol wrap{}(SortFoo{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        endmodule []"#,
    )
    .expect("the fixture loads");
    let one = r#"\dv{SortInt{}}("1")"#;
    let mut failures = Vec::new();
    for (pattern, well_sorted) in [
        (r"inj{SortFoo{}, SortKItem{}}(c{}())".to_owned(), true),
        (format!("inj{{SortInt{{}}, SortKItem{{}}}}({one})"), true),
        (r"inj{SortSub{}, SortKItem{}}(s{}())".to_owned(), true),
        (format!("inj{{SortFoo{{}}, SortKItem{{}}}}({one})"), false),
        (r"inj{SortInt{}, SortKItem{}}(c{}())".to_owned(), false),
        (r"inj{SortFoo{}, SortKItem{}}(s{}())".to_owned(), false),
        (r"wrap{}(c{}())".to_owned(), true),
        (format!("wrap{{}}({one})"), false),
    ] {
        let syntax = parse_pattern(&pattern).expect("the pattern parses");
        let verified = definition.verify_standalone_pattern(&syntax, &[]).is_ok();
        let internalized = definition
            .admit_unverified(&syntax, &[])
            .internalize_term()
            .is_ok();
        if verified != well_sorted || internalized != well_sorted {
            failures.push(format!(
                "{pattern}: well-sorted {well_sorted}, verified {verified}, internalized \
                 unverified {internalized}"
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
