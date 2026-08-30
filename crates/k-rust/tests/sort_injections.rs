use indoc::indoc;
use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
};
use k_rust::inner::resolve_rule_bubbles;
use k_rust::kast::{Label, Sort, Term, TermMetadata};
use k_rust::kompile::{
    SortInjector, add_sort_injections_to_definition, generate_sort_projections,
    resolve_semantic_casts, term_to_kore_from_resolved,
};
use k_rust::kore::printer::Printer;

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
    let definition = resolve_semantic_casts(&lowered(source));
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
