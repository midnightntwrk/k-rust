use indoc::indoc;
use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE, ProductionItem,
    ResolvedDefinition, SOURCE_ATTRIBUTE, Sentence,
};
use k_rust::inner::resolve_rule_bubbles;
use k_rust::kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata};
use k_rust::kompile::{
    SortInjectionError, SortInjector, add_sort_injections_to_definition, generate_sort_projections,
    term_to_kore_from_resolved,
};
use k_rust::kore::printer::Printer;
use k_rust::provenance::{GeneratingPass, ORIGIN_ATTRIBUTE};
use serde_json::json;

fn lowered(source: &str) -> Definition {
    let parsed = k_rust::outer::parse("injections.k", source).expect("definition should parse");
    let definition = k_rust::outer::lower(&parsed, "MAIN").expect("definition should lower");
    resolve_rule_bubbles(&definition).expect("rule bubbles should resolve")
}

#[derive(Debug)]
#[allow(dead_code)]
struct InjectionSummary {
    injected: String,
    kore: String,
}

macro_rules! injection_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let definition = generate_sort_projections(&lowered(source))
                .expect("sort projections should generate");
            let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
            let injector = SortInjector::new(&resolved, "MAIN").expect("injector should build");
            let summaries = definition
                .main_module()
                .expect("main module should exist")
                .local_sentences
                .iter()
                .filter(|sentence| {
                    matches!(sentence, Sentence::Rule { .. } | Sentence::Claim { .. })
                        && sentence.attributes().get("projection").is_none()
                })
                .map(|sentence| {
                    let injected = injector
                        .inject_sentence(sentence)
                        .expect("sort injections should succeed");
                    let body = match &injected {
                        Sentence::Rule { body, .. } | Sentence::Claim { body, .. } => body,
                        _ => unreachable!(),
                    };
                    let kore = term_to_kore_from_resolved(&resolved, "MAIN", body)
                        .expect("injected term should convert to KORE");
                    InjectionSummary {
                        injected: body.to_string(),
                        kore: Printer::pretty(100).print_pattern(&kore),
                    }
                })
                .collect::<Vec<_>>();
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(summaries);
            });
        }
    };
}

#[test]
fn reference_constructor_arguments_inject_only_a_strict_subsort() {
    // reference: kast --definition ref --module MAIN --sort Box --output kore -e 'box(small)'
    let definition = lowered(include_str!(
        "fixtures/reference/injections/arguments/test.k"
    ));
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    for (argument, expected) in [
        (
            "small",
            include_str!("fixtures/reference/injections/arguments/subsort.kore"),
        ),
        (
            "large",
            include_str!("fixtures/reference/injections/arguments/exact-sort.kore"),
        ),
    ] {
        let term = Term::apply("box", vec![Term::apply(argument, vec![])]);
        let injected = injector.inject_at_top(&term).unwrap();
        let actual = term_to_kore_from_resolved(&resolved, "MAIN", &injected).unwrap();
        let expected = k_rust::kore::parser::parse_pattern(expected).unwrap();
        assert_eq!(actual, expected, "argument {argument}");
    }
}

#[test]
fn recovers_a_stale_catalog_identity_for_a_unique_label() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(module);
    let stale = catalog.productions_for(&k_rust::definition::LabelHead::new("b"))[0];
    let term = Term::apply("a", Vec::new()).with_metadata(TermMetadata {
        span: None,
        production: Some(ResolvedProductionId(stale.0)),
        sort: None,
        origin: None,
    });
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    assert_eq!(
        injector.inject_at_top(&term).unwrap().to_string(),
        "a(.KList)"
    );
}

#[test]
fn stale_catalog_identity_uses_metadata_sort_to_disambiguate_a_label() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(choice)]
          syntax B ::= "b" [symbol(choice)]
          syntax Stale ::= "stale" [symbol(stale)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(module);
    let stale = catalog.productions_for(&k_rust::definition::LabelHead::new("stale"))[0];
    let term = Term::apply("choice", Vec::new()).with_metadata(TermMetadata {
        span: None,
        production: Some(ResolvedProductionId(stale.0)),
        sort: Some(Sort::new("A")),
        origin: None,
    });
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    assert_eq!(
        injector.inject_at_top(&term).unwrap().to_string(),
        "choice(.KList)"
    );
}

#[test]
fn config_dependent_sort_predicate_has_the_reference_error() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Bool
          syntax Exp
          syntax Bool ::= isExp(Exp) [function, symbol(isExp)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let term = Term::apply(
        "isExp",
        vec![Term::variable("X"), Term::variable("THIS_CONFIGURATION")],
    );
    let error = injector
        .inject_at_top(&term)
        .expect_err("configuration-dependent predicates must be rejected");
    assert_eq!(
        error.to_string(),
        "Invalid sort predicate isExp that depends directly or indirectly on the current configuration. Is it possible to replace the sort predicate with a regular function?"
    );
}

#[test]
fn reconstructs_a_singleton_user_list_for_generated_terms() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Item ::= "item" [symbol(item)]
          syntax Items ::= List{Item, ""} [symbol(items), terminator-symbol(.Items)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let item = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Item")),
    };

    let injected = injector.inject(&item, &Sort::new("Items")).unwrap();

    assert_eq!(injected.to_string(), "items(X,`.Items`(.KList))");
}

injection_snapshot!(
    inserts_subsort_injections_in_production_arguments,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Stmt ::= "print" Exp [symbol(print)]

          rule print 1 => print 2
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
#[test]
fn semantic_casts_instantiate_parametric_production_results() {
    let source = indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax C ::= A | B
          syntax D ::= A | B
          syntax {S} S ::= "pair(" S "," S ")" [symbol(pair)]

          rule pair(a, b):C => pair(a, b):C
        endmodule
    "#};
    let definition = k_rust::kompile::resolve_semantic_casts(&lowered(source));
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let rule = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(sentence, Sentence::Rule { .. }))
        .unwrap();
    let injected = injector.inject_sentence(rule).unwrap();
    let Sentence::Rule { body, .. } = injected else {
        unreachable!()
    };
    let rendered = body.to_string();

    assert_eq!(rendered.matches("pair{C}").count(), 2, "{rendered}");
    assert_eq!(rendered.matches("inj{A,C}").count(), 2, "{rendered}");
    assert_eq!(rendered.matches("inj{B,C}").count(), 2, "{rendered}");
}

#[test]
fn parametric_head_matches_declared_subsort_of_actual() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax Value ::= MInt{8}
          syntax Result
          syntax {W} Result ::= "use(" MInt{W} ")" [symbol(use)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let term = Term::apply(
        "use",
        vec![Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("Value")),
        }],
    );

    let injected = injector.inject(&term, &Sort::new("Result")).unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric use application");
    };

    assert_eq!(label.parameters, vec![Sort::new("8")]);
    assert!(matches!(
        arguments.as_slice(),
        [Term::Apply { label, .. }]
            if label.name == "inj"
                && label.parameters == vec![Sort::new("Value"), Sort::with_parameters("MInt", vec![Sort::new("8")])]
    ));
}

fn wem10_bound_definition(source: &str) -> ResolvedDefinition {
    ResolvedDefinition::resolve(&lowered(source)).unwrap()
}

fn wem10_bound_injector() -> ResolvedDefinition {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax KItem ::= MInt{8}
          syntax K
          syntax K ::= KItem
          syntax KBott
          syntax KItem ::= KBott
          syntax KList
          syntax KList ::= K
        endmodule
    "#});
    ResolvedDefinition::resolve(&definition).unwrap()
}

fn rewrite_tokens(left: Sort, right: Sort) -> Term {
    Term::Rewrite {
        left: Box::new(Term::Token {
            token: "left".into(),
            sort: left,
        }),
        right: Box::new(Term::Token {
            token: "right".into(),
            sort: right,
        }),
    }
}

#[test]
fn wem10_bound_resolves_unfixed_parametric_entry_through_declared_instantiations() {
    let definition = wem10_bound_injector();
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let unresolved = Sort::with_parameters(
        "MInt",
        vec![Sort::with_parameters("#SortParam", vec![Sort::new("Q")])],
    );
    let rewrite = rewrite_tokens(unresolved.clone(), unresolved);

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::with_parameters("MInt", vec![Sort::new("8")])
    );
}

#[test]
fn wem10_bound_filters_concrete_seed_bounds_through_declared_instantiations() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax Int
          syntax Bool
          syntax Box{Int}
          syntax Box{Bool}
          syntax Seed
          syntax Good ::= Seed
          syntax Good ::= Box{Int}
          syntax Decoy ::= Seed
          syntax K ::= Good
          syntax K ::= Decoy
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let unresolved = Sort::with_parameters(
        "Box",
        vec![Sort::with_parameters("#SortParam", vec![Sort::new("Q")])],
    );
    let rewrite = rewrite_tokens(unresolved, Sort::new("Seed"));

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("Good")
    );
}

#[test]
fn wem10_bound_excludes_kbott_and_lower_parser_sorts() {
    let definition = wem10_bound_injector();
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("KBott"), Sort::new("KBott"));

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("KItem")
    );
}

#[test]
fn wem10_bound_excludes_a_strict_lower_parser_sort() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax ParserLow ::= A
          syntax ParserLow ::= B
          syntax KBott ::= ParserLow
          syntax KItem ::= KBott
          syntax K ::= KItem
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("KItem")
    );
}

#[test]
fn wem10_bound_rejects_sorts_above_k() {
    let definition = wem10_bound_injector();
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("KList"), Sort::new("KList"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_rejects_a_distinct_common_bound_above_k() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax K
          syntax Above ::= A
          syntax Above ::= B
          syntax Above ::= K
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_retains_a_relation_free_singleton() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("A"));

    assert_eq!(injector.term_sort(&rewrite, None).unwrap(), Sort::new("A"));
}

#[test]
fn wem10_bound_retains_a_unique_semantic_bound() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax C ::= A
          syntax C ::= B
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert_eq!(injector.term_sort(&rewrite, None).unwrap(), Sort::new("C"));
}

#[test]
fn wem10_bound_rejects_ambiguous_minima() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax C ::= A
          syntax C ::= B
          syntax D ::= A
          syntax D ::= B
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_rejects_absent_common_bound() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_preserves_the_expected_sort_ceiling() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax C ::= A
          syntax C ::= B
          syntax D ::= C
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert_eq!(
        injector.term_sort(&rewrite, Some(&Sort::new("D"))).unwrap(),
        Sort::new("C")
    );
    assert!(matches!(
        injector.term_sort(&rewrite, Some(&Sort::new("A"))),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn semantic_casts_project_heterogeneous_collection_results() {
    let mut definition = lowered(indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token]
          syntax Int ::= r"[0-9]+" [token]
          syntax List
          syntax Map
          syntax KItem ::= List "[" Int "]" [function, hook(LIST.get), symbol(List:get)]
          syntax KItem ::= Map "[" Int "]" [function, hook(MAP.lookup), symbol(Map:lookup)]
        endmodule
    "#});
    let truth = || Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let get = |label: &str, collection_sort: &str| {
        Term::apply(
            "#SemanticCastToInt",
            vec![Term::apply(
                label,
                vec![
                    Term::Variable {
                        name: "COLLECTION".into(),
                        sort: Some(Sort::new(collection_sort)),
                    },
                    Term::Token {
                        token: "0".into(),
                        sort: Sort::new("Int"),
                    },
                ],
            )],
        )
    };
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == definition.main_module)
        .unwrap();
    module.local_sentences.extend([
        Sentence::Rule {
            body: get("List:get", "List"),
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        },
        Sentence::Rule {
            body: get("Map:lookup", "Map"),
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        },
    ]);

    let definition = k_rust::kompile::resolve_semantic_casts(&definition);
    let definition = k_rust::kompile::subsort_kitem(&definition).unwrap();
    let definition = generate_sort_projections(&definition).unwrap();
    let definition = add_sort_injections_to_definition(&definition).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let summaries = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("projection").is_none() => Some((
                body.to_string(),
                Printer::pretty(100)
                    .print_pattern(&term_to_kore_from_resolved(&resolved, "MAIN", body).unwrap()),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::assert_debug_snapshot!(summaries, @r###"
    [
        (
            "inj{Int,KItem}(`project:Int`(`List:get`(COLLECTION,#token(\"0\",\"Int\"))))",
            "inj{SortInt{}, SortKItem{}}(\n  Lblproject'Coln'Int{}(\n    kseq{}(LblList'Coln'get{}(VarCOLLECTION:SortList{}, \\dv{SortInt{}}(\"0\")), dotk{}())\n  )\n)",
        ),
        (
            "inj{Int,KItem}(`project:Int`(`Map:lookup`(COLLECTION,#token(\"0\",\"Int\"))))",
            "inj{SortInt{}, SortKItem{}}(\n  Lblproject'Coln'Int{}(\n    kseq{}(LblMap'Coln'lookup{}(VarCOLLECTION:SortMap{}, \\dv{SortInt{}}(\"0\")), dotk{}())\n  )\n)",
        ),
    ]
    "###);
}

injection_snapshot!(
    injects_sequence_items_through_kitem,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]

          rule 1 ~> 2 => 2 ~> 1
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
injection_snapshot!(
    substitutes_parametric_production_signatures,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Box ::= "box(" Exp ")" [symbol(box)]
          syntax {S} S ::= "same(" S ")" [symbol(same)]

          rule box(same(1)) => box(1)
        endmodule
    "#
);

injection_snapshot!(
    preserves_semantic_cast_variable_context,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]

          rule X:Exp + 0 => X:Exp
        endmodule
    "#
);

injection_snapshot!(
    injects_semantically_cast_tokens_from_their_intrinsic_sort,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]

          rule 1:KItem => 2:KItem
        endmodule
    "#
);

injection_snapshot!(
    handles_parser_generated_outer_casts,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [token]
          syntax Exp ::= Id

          rule X:Exp => {X}:>Exp
        endmodule
    "#
);

injection_snapshot!(
    uses_resolved_overloaded_productions,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Result ::= "left" A [symbol(pick)]
                          | "right" B [symbol(pick)]
          syntax Value ::= A | B | Result
          syntax Wrapper ::= "wrap" Value [symbol(wrap)]

          rule wrap left a => wrap right b
        endmodule
    "#
);

injection_snapshot!(
    wraps_cell_sorts_with_set_elements,
    r#"
        module MAIN
          syntax Cell ::= "cell" [symbol(cell)]
          syntax Cells [hook(SET.Set)]
          syntax Cells ::= Cell
                         | "CellItem" "(" Cell ")" [symbol(CellItem), hook(SET.element)]
                         | Cells Cells [symbol(_Cells_), hook(SET.concat), comm, idem, element(CellItem), wrapElement(cell)]
          syntax Parent ::= "parent" Cells [symbol(parent)]

          rule parent cell => parent cell
        endmodule
    "#
);

injection_snapshot!(
    wraps_cell_sorts_with_map_keys_and_elements,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Entry ::= "entry" Int [symbol(entry)]
          syntax Entries [hook(MAP.Map)]
          syntax Entries ::= Entry
                           | "EntryItem" "(" Int "," Entry ")" [symbol(EntryItem), hook(MAP.element)]
                           | Entries Entries [symbol(_Entries_), hook(MAP.concat), comm, element(EntryItem), wrapElement(entry)]
          syntax Parent ::= "parent" Entries [symbol(parent)]

          rule parent entry 1 => parent entry 2
        endmodule
    "#
);

#[test]
fn lifts_nested_rewrites_before_adding_injections() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= "pair" "(" Exp "," Exp ")" [symbol(pair)]
        endmodule
    "#});
    let token = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    };
    let body = Term::apply(
        "pair",
        vec![
            Term::Rewrite {
                left: Box::new(token("1")),
                right: Box::new(token("2")),
            },
            token("3"),
        ],
    );
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let sentence = Sentence::Rule {
        body,
        requires: truth.clone(),
        ensures: truth,
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject_sentence(&sentence)
        .unwrap();
    let Sentence::Rule { body, .. } = injected else {
        unreachable!()
    };
    assert_eq!(
        body.to_string(),
        "pair(inj{Int,Exp}(#token(\"1\",\"Int\")),inj{Int,Exp}(#token(\"3\",\"Int\")))=>pair(inj{Int,Exp}(#token(\"2\",\"Int\")),inj{Int,Exp}(#token(\"3\",\"Int\")))"
    );
}

#[test]
fn definition_sort_injections_carry_generation_receipts() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
                       | "pair" "(" Exp "," Exp ")" [symbol(pair)]
          rule pair(1, 3) => pair(2, 3) [label(injected)]
        endmodule
    "#});
    let injected = add_sort_injections_to_definition(&definition).unwrap();
    let receipt = injected
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| {
            (sentence.attributes().get_str("label") == Some("injected"))
                .then(|| sentence.attributes().get(ORIGIN_ATTRIBUTE))
                .flatten()
        })
        .expect("the injected rule should carry a receipt");

    assert_eq!(receipt["pass"], GeneratingPass::AddSortInjections.as_str());
}

#[test]
fn kitem_to_k_uses_a_sequence_without_an_injection() {
    let definition = lowered("module MAIN\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let term = Term::InjectedLabel(Label::new("label"));
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject(&term, &Sort::new("K"))
        .unwrap();

    assert!(matches!(
        injected,
        Term::Sequence(ref items)
            if matches!(items.as_slice(), [Term::InjectedLabel(label)] if label.name == "label")
    ));
}

#[test]
fn application_cast_context_does_not_replace_its_production_sort() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax KItem ::= "project" [symbol(project)]
          syntax Cell ::= "cell" K [symbol(cell)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let projected = Term::apply("project", vec![]).with_metadata(TermMetadata {
        sort: Some(Sort::new("K")),
        ..TermMetadata::default()
    });
    let term = Term::apply("cell", vec![projected]);
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject_at_top(&term)
        .unwrap();

    let Term::Apply { arguments, .. } = injected.unannotated() else {
        panic!("expected cell application");
    };
    assert!(matches!(
        arguments.as_slice(),
        [Term::Sequence(items)]
            if matches!(items.as_slice(), [item]
                if matches!(item.unannotated(), Term::Apply { label, .. } if label.name == "project"))
    ));
}

#[test]
fn synthetic_unsorted_variables_use_expected_sort_then_k() {
    let definition = lowered("module MAIN\n  syntax Exp\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let variable = Term::variable("X");

    assert_eq!(injector.term_sort(&variable, None).unwrap(), Sort::new("K"));
    assert_eq!(
        injector
            .term_sort(&variable, Some(&Sort::new("Exp")))
            .unwrap(),
        Sort::new("Exp")
    );
    assert!(matches!(
        injector.inject(&variable, &Sort::new("Exp")).unwrap(),
        Term::Variable { name, sort: Some(sort) } if name == "X" && sort == Sort::new("Exp")
    ));
    assert!(matches!(
        injector.inject_at_top(&variable).unwrap(),
        Term::Variable { name, sort: Some(sort) } if name == "X" && sort == Sort::new("K")
    ));
}

#[test]
fn synthetic_application_sort_metadata_projects_only_strict_subsorts() {
    let definition = generate_sort_projections(&lowered(indoc! {r#"
        module MAIN
          syntax Int ::= "int" [symbol(int)]
          syntax KItem ::= Int
                         | "item" [symbol(item)]
          syntax Other ::= "other" [symbol(other)]
        endmodule
    "#}))
    .unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let metadata = |sort| TermMetadata {
        sort: Some(Sort::new(sort)),
        ..TermMetadata::default()
    };

    let exact = Term::apply("item", vec![]).with_metadata(metadata("KItem"));
    let upcast = Term::apply("int", vec![]).with_metadata(metadata("KItem"));
    let downcast = Term::apply("item", vec![]).with_metadata(metadata("Int"));
    let unrelated = Term::apply("item", vec![]).with_metadata(metadata("Other"));

    let exact = injector.inject_at_top(&exact).unwrap().to_string();
    let upcast = injector
        .inject(&upcast, &Sort::new("KItem"))
        .unwrap()
        .to_string();
    let downcast = injector.inject_at_top(&downcast).unwrap().to_string();
    let unrelated = injector.inject_at_top(&unrelated).unwrap().to_string();

    assert_eq!(exact, "item(.KList)");
    assert_eq!(upcast, "inj{Int,KItem}(int(.KList))");
    assert_eq!(downcast, "inj{Int,KItem}(`project:Int`(item(.KList)))");
    assert_eq!(unrelated, "item(.KList)");
}

#[test]
fn flattens_nested_sequences_during_final_injection() {
    let definition = lowered("module MAIN\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let term = Term::Sequence(vec![
        Term::Sequence(vec![Term::InjectedLabel(Label::new("first"))]),
        Term::Variable {
            name: "REST".into(),
            sort: Some(Sort::new("K")),
        },
    ]);
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject(&term, &Sort::new("K"))
        .unwrap();

    assert!(matches!(
        injected,
        Term::Sequence(ref items) if items.len() == 2
    ));
}

#[test]
fn definition_injection_uses_the_selected_modules_visible_syntax() {
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "BASE".into(),
                imports: vec![],
                local_sentences: vec![Sentence::Rule {
                    body: Term::Rewrite {
                        left: Box::new(Term::apply("consumerOnly", vec![])),
                        right: Box::new(Term::apply("consumerOnly", vec![])),
                    },
                    requires: truth.clone(),
                    ensures: truth,
                    attributes: Attributes::default(),
                }],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "BASE".into(),
                    public: true,
                }],
                local_sentences: vec![Sentence::Production {
                    label: Some(Label::new("consumerOnly")),
                    parameters: vec![],
                    sort: Sort::new("KItem"),
                    items: Vec::<ProductionItem>::new(),
                    attributes: Attributes::default(),
                }],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };

    let injected = add_sort_injections_to_definition(&definition).unwrap();
    let Sentence::Rule { body, .. } = &injected.modules[0].local_sentences[0] else {
        panic!("expected imported rule");
    };
    assert_eq!(
        body.to_string(),
        "consumerOnly(.KList)=>consumerOnly(.KList)"
    );
}

#[test]
fn definition_injection_ignores_modules_outside_the_main_import_closure() {
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let unrelated_module = FlatModule {
        name: "UNRELATED".into(),
        imports: vec![],
        local_sentences: vec![Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply("unrelated", vec![])),
                right: Box::new(Term::apply("unrelated", vec![])),
            },
            requires: truth.clone(),
            ensures: truth,
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "MAIN".into(),
                imports: vec![],
                local_sentences: vec![],
                attributes: Attributes::default(),
            },
            unrelated_module.clone(),
        ],
        attributes: Attributes::default(),
    };

    let injected = add_sort_injections_to_definition(&definition).unwrap();

    assert_eq!(injected.modules[1], unrelated_module);
}

#[test]
fn definition_injection_errors_name_the_source_sentence() {
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let mut attributes = Attributes::default();
    attributes.insert(SOURCE_ATTRIBUTE, json!("fixture.k"));
    attributes.insert(LOCATION_ATTRIBUTE, json!([17, 3, 17, 18]));
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: vec![],
            local_sentences: vec![Sentence::Rule {
                body: Term::Rewrite {
                    left: Box::new(Term::apply("missing", vec![])),
                    right: Box::new(Term::apply("missing", vec![])),
                },
                requires: truth.clone(),
                ensures: truth,
                attributes,
            }],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };

    let error = add_sort_injections_to_definition(&definition).unwrap_err();

    assert_eq!(
        error.to_string(),
        "fixture.k:17: cannot find a production for KLabel \"missing\""
    );
}
