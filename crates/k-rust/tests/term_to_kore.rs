use indoc::indoc;
use k_rust::definition::{Definition, LabelHead, ResolvedDefinition, Sentence};
use k_rust::inner::resolve_rule_bubbles;
use k_rust::kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata};
use k_rust::kompile::{TermConverter, term_to_kore};
use k_rust::kore::parser::parse_pattern;
use k_rust::kore::printer::Printer;
use k_rust::outer;

fn lowered(source: &str) -> Definition {
    let parsed = outer::parse("terms.k", source).expect("definition should parse");
    outer::lower(&parsed, "MAIN").expect("definition should lower")
}

fn rules(source: &str) -> Definition {
    resolve_rule_bubbles(&lowered(source)).expect("rule bubbles should resolve")
}

macro_rules! term_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let definition = rules(source);
            let emitted = definition
                .main_module()
                .expect("main module should exist")
                .local_sentences
                .iter()
                .filter_map(|sentence| match sentence {
                    Sentence::Rule { body, .. } | Sentence::Claim { body, .. } => Some(body),
                    _ => None,
                })
                .map(|body| {
                    let pattern = term_to_kore(&definition, "MAIN", body)
                        .expect("term should convert to KORE");
                    let printed = Printer::pretty(100).print_pattern(&pattern);
                    assert_eq!(
                        parse_pattern(&printed).expect("emitted KORE pattern should reparse"),
                        pattern,
                    );
                    printed
                })
                .collect::<Vec<_>>()
                .join("\n\n");
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(emitted);
            });
        }
    };
}

term_snapshot!(
    converts_rewrites_applications_and_domain_values,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]

          rule X:Exp + 0 => X:Exp
        endmodule
    "#
);

term_snapshot!(
    converts_k_sequences,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int

          rule X:Exp ~> Y:Exp => Y:Exp ~> X:Exp
        endmodule
    "#
);

term_snapshot!(
    converts_a_resolved_overloaded_application,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Result ::= "left" A [symbol(pick)]
                          | "right" B [symbol(pick)]

          rule left a => left a
        endmodule
    "#
);

#[test]
fn converts_ml_connectives_and_set_variables() {
    let definition = lowered("module MAIN\nendmodule");
    let sort = Sort::new("S");
    let variable = Term::Variable {
        name: "X".into(),
        sort: Some(sort.clone()),
    };
    let term = Term::Apply {
        label: Label::with_parameters("#Exists", vec![sort.clone(), sort.clone()]),
        arguments: vec![
            variable.clone(),
            Term::Apply {
                label: Label::with_parameters("#And", vec![sort]),
                arguments: vec![variable],
            },
        ],
    };
    let pattern = term_to_kore(&definition, "MAIN", &term).expect("ML term should convert");
    assert_eq!(
        Printer::compact().print_pattern(&pattern),
        "\\exists{SortS{}}(VarX:SortS{}, \\and{SortS{}}(VarX:SortS{}))"
    );
    let set_variable = Term::Variable {
        name: "@SET".into(),
        sort: Some(Sort::new("S")),
    };
    assert_eq!(
        Printer::compact().print_pattern(
            &term_to_kore(&definition, "MAIN", &set_variable).expect("set variable should convert")
        ),
        "@VarSET:SortS{}"
    );
}

#[test]
fn converts_sequences_using_item_sorts() {
    let definition = lowered("module MAIN\nendmodule");
    let term = Term::Sequence(vec![
        Term::Variable {
            name: "ITEM".into(),
            sort: Some(Sort::new("KItem")),
        },
        Term::Variable {
            name: "REST".into(),
            sort: Some(Sort::new("K")),
        },
    ]);
    let pattern = term_to_kore(&definition, "MAIN", &term).expect("sequence should convert");
    assert_eq!(
        Printer::compact().print_pattern(&pattern),
        "kseq{}(VarITEM:SortKItem{}, VarREST:SortK{})"
    );
}

#[test]
fn recovers_parameterized_semantic_cast_sorts() {
    let definition = lowered("module MAIN\nendmodule");
    let cast = Term::Apply {
        label: Label::new("#SemanticCastToMInt{8}"),
        arguments: vec![Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("K")),
        }],
    };
    let term = Term::Rewrite {
        left: Box::new(cast.clone()),
        right: Box::new(cast),
    };
    let pattern = term_to_kore(&definition, "MAIN", &term).unwrap();
    assert!(matches!(
        pattern,
        k_rust::kore::ast::Pattern::Rewrites {
            sort: k_rust::kore::ast::Sort::Application { ref name, ref arguments },
            ..
        } if name == "SortMInt" && arguments == &[k_rust::kore::ast::Sort::Application {
            name: "Sort8".into(),
            arguments: Vec::new(),
        }]
    ));
}

#[test]
fn decodes_string_and_bytes_token_syntax() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax String [hook(STRING.String)]
          syntax Bytes [hook(BYTES.Bytes)]
        endmodule
    "#});
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    let converter = TermConverter::new(&resolved, "MAIN").unwrap();
    for (term, expected) in [
        (
            Term::Token {
                token: r#""line\nα""#.into(),
                sort: Sort::new("String"),
            },
            "\\dv{SortString{}}(\"line\\n\\u03b1\")",
        ),
        (
            Term::Token {
                token: r#"b"bytes\x21""#.into(),
                sort: Sort::new("Bytes"),
            },
            "\\dv{SortBytes{}}(\"bytes!\")",
        ),
    ] {
        assert_eq!(
            Printer::compact().print_pattern(&converter.convert(&term).unwrap()),
            expected
        );
    }
}

#[test]
fn resolved_production_identity_disambiguates_application_sorts() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(choice)]
          syntax B ::= "b" [symbol(choice)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(module);
    let production = catalog.productions_for(&LabelHead::new("choice"))[0];
    let annotated = Term::apply("choice", vec![]).with_metadata(TermMetadata {
        span: None,
        production: Some(ResolvedProductionId(production.0)),
    });
    let term = Term::Rewrite {
        left: Box::new(annotated.clone()),
        right: Box::new(annotated),
    };

    let pattern = TermConverter::new(&resolved, "MAIN")
        .unwrap()
        .convert(&term)
        .expect("selected production should recover the application sort");
    assert!(matches!(
        pattern,
        k_rust::kore::ast::Pattern::Rewrites { .. }
    ));
}
