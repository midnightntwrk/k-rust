use indoc::indoc;
use k_rust::definition::{Definition, LabelHead, ResolvedDefinition, Sentence};
use k_rust::inner::resolve_rule_bubbles;
use k_rust::kast::{Label, Sort, Term, TermMetadata};
use k_rust::kompile::{TermConversionError, TermConverter, term_to_kore};
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
                .filter_map(|sentence| match &**sentence {
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

fn sorted_variable(name: &str, sort: &str) -> Term {
    Term::Variable {
        name: name.into(),
        sort: Some(Sort::new(sort)),
    }
}

fn anonymous_quantifier(label: &str, body: Term) -> Term {
    Term::Apply {
        label: Label::with_parameters(label, vec![Sort::new("Int"), Sort::new("Bool")]),
        arguments: vec![sorted_variable("_Gen0", "Int"), body],
    }
}

fn convert_handbuilt(term: &Term) -> Result<String, TermConversionError> {
    let definition = lowered("module MAIN\nendmodule");
    term_to_kore(&definition, "MAIN", term)
        .map(|pattern| Printer::compact().print_pattern(&pattern))
}

// A quantifier binds exactly its own variable: the spelling of a resolved anonymous variable
// (`_Gen<n>`) has no bearing on what a binder binds.
#[test]
fn a_binder_spelled_as_generated_binds_only_its_own_variable() {
    let term = anonymous_quantifier(
        "#Exists",
        Term::apply(
            "p",
            vec![
                sorted_variable("X", "Int"),
                sorted_variable("_Gen0", "Int"),
                sorted_variable("_Gen1", "Int"),
            ],
        ),
    );

    assert_eq!(
        convert_handbuilt(&term).unwrap(),
        "\\exists{SortBool{}}(Var'Unds'Gen0:SortInt{}, Lblp{}(VarX:SortInt{}, Var'Unds'Gen0:SortInt{}, Var'Unds'Gen1:SortInt{}))"
    );
}

#[test]
fn a_binder_whose_variable_its_body_does_not_mention_is_emitted_as_written() {
    let term = anonymous_quantifier(
        "#Exists",
        Term::apply(
            "p",
            vec![sorted_variable("X", "Int"), sorted_variable("_Gen1", "Int")],
        ),
    );

    assert_eq!(
        convert_handbuilt(&term).unwrap(),
        "\\exists{SortBool{}}(Var'Unds'Gen0:SortInt{}, Lblp{}(VarX:SortInt{}, Var'Unds'Gen1:SortInt{}))"
    );
}

#[test]
fn nested_binders_spelled_as_generated_each_bind_their_own_variable() {
    let inner = Term::Apply {
        label: Label::with_parameters("#Forall", vec![Sort::new("Bool"), Sort::new("Bool")]),
        arguments: vec![
            sorted_variable("_Gen2", "Bool"),
            Term::apply(
                "p",
                vec![
                    sorted_variable("_Gen2", "Bool"),
                    sorted_variable("_Gen0", "Int"),
                    sorted_variable("_Gen1", "Int"),
                ],
            ),
        ],
    };
    let term = anonymous_quantifier("#Exists", inner);

    assert_eq!(
        convert_handbuilt(&term).unwrap(),
        "\\exists{SortBool{}}(Var'Unds'Gen0:SortInt{}, \\forall{SortBool{}}(Var'Unds'Gen2:SortBool{}, Lblp{}(Var'Unds'Gen2:SortBool{}, Var'Unds'Gen0:SortInt{}, Var'Unds'Gen1:SortInt{})))"
    );
}

/// Every anonymous variable is named before conversion (`resolve anonymous variables`), so an
/// unresolved `_` binder reaching the converter is a compiler defect.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "reached KORE conversion before anonymous resolution")]
fn an_unresolved_anonymous_binder_is_a_debug_assertion() {
    let term = Term::Apply {
        label: Label::with_parameters("#Exists", vec![Sort::new("Int"), Sort::new("Bool")]),
        arguments: vec![
            sorted_variable("_", "Int"),
            Term::apply("p", vec![sorted_variable("X", "Int")]),
        ],
    };
    let _ = convert_handbuilt(&term);
}

#[test]
fn named_binders_keep_the_single_variable_translation() {
    let term = Term::Apply {
        label: Label::with_parameters("#Exists", vec![Sort::new("Int"), Sort::new("Bool")]),
        arguments: vec![
            sorted_variable("X", "Int"),
            Term::apply("p", vec![sorted_variable("X", "Int")]),
        ],
    };

    assert_eq!(
        convert_handbuilt(&term).unwrap(),
        "\\exists{SortBool{}}(VarX:SortInt{}, Lblp{}(VarX:SortInt{}))"
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
fn retained_injection_checks_the_emitted_operand_sort_before_placement_metadata() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax KList ::= K
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let converter = TermConverter::new(&resolved, "MAIN").unwrap();
    let variable = sorted_variable("X", "B");
    for (operand, source, target) in [
        (variable.clone(), "B", "KItem"),
        (Term::Sequence(vec![]), "K", "KList"),
        (
            Term::Rewrite {
                left: Box::new(variable.clone()),
                right: Box::new(variable.clone()),
            },
            "B",
            "KItem",
        ),
        (
            Term::As {
                pattern: Box::new(variable.clone()),
                alias: Box::new(variable),
            },
            "B",
            "KItem",
        ),
    ] {
        let operand = operand.with_metadata(TermMetadata {
            sort: Some(Sort::new("A")),
            ..TermMetadata::default()
        });
        let injection = |source, target| Term::Apply {
            label: Label::with_parameters("inj", vec![Sort::new(source), Sort::new(target)]),
            arguments: vec![operand.clone()],
        };
        assert!(matches!(
            converter.convert(&injection("A", "KItem")),
            Err(TermConversionError::InvalidBuiltin { .. })
        ));
        converter
            .convert(&injection(source, target))
            .expect("the operand's emitted sort licenses the injection despite placement metadata");
    }
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
          syntax String [hook(STRING.String), token]
          syntax Bytes [hook(BYTES.Bytes), token]
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
        // A `String` escape names a code point: `"\xe9"` and `"é"` are one value, and
        // `"\xc3\xa9"` is two code points.
        (
            Term::Token {
                token: r#""é\xe9\xc3\xa9""#.into(),
                sort: Sort::new("String"),
            },
            "\\dv{SortString{}}(\"\\xe9\\xe9\\xc3\\xa9\")",
        ),
        (
            Term::Token {
                token: r#"b"bytes\x21""#.into(),
                sort: Sort::new("Bytes"),
            },
            "\\dv{SortBytes{}}(\"bytes!\")",
        ),
        (
            Term::Token {
                token: r#"b"\xe9""#.into(),
                sort: Sort::new("Bytes"),
            },
            "\\dv{SortBytes{}}(\"\\xe9\")",
        ),
    ] {
        assert_eq!(
            Printer::compact().print_pattern(&converter.convert(&term).unwrap()),
            expected
        );
    }
}

/// A KORE domain value outside a definition carries only its sort's name, so its payload is
/// stored by the encoding of that name (`LiteralEncoding`: bytes for `SortBytes`, UTF-8 code
/// points for every other sort). A token of a sort hooked `BYTES.Bytes` under another name holds
/// the code points of its bytes' values like any `Bytes` token, stored as that name's encoding
/// says, so its KORE text reads back as the same payload and distinct byte strings stay
/// distinct; the KAST converter gives the token back.
#[test]
fn stores_each_token_by_the_encoding_of_its_kore_sort() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Bytes [hook(BYTES.Bytes), token]
          syntax MyBytes [hook(BYTES.Bytes), token]
        endmodule
    "#});
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    let converter = TermConverter::new(&resolved, "MAIN").unwrap();
    let hooks = [
        ("Bytes".to_owned(), "BYTES.Bytes".to_owned()),
        ("MyBytes".to_owned(), "BYTES.Bytes".to_owned()),
    ]
    .into_iter()
    .collect::<std::collections::HashMap<_, _>>();
    let back = k_rust::kast::convert::Converter::new(&hooks);
    for (sort, token, expected) in [
        ("MyBytes", r#"b"\xe9""#, r#"\dv{SortMyBytes{}}("\xe9")"#),
        (
            "MyBytes",
            r#"b"\xc3\xa9""#,
            r#"\dv{SortMyBytes{}}("\xc3\xa9")"#,
        ),
        ("Bytes", r#"b"\xe9""#, r#"\dv{SortBytes{}}("\xe9")"#),
        ("Bytes", r#"b"\xc3\xa9""#, r#"\dv{SortBytes{}}("\xc3\xa9")"#),
    ] {
        let term = Term::Token {
            token: token.into(),
            sort: Sort::new(sort),
        };
        let pattern = converter.convert(&term).unwrap();
        let printed = Printer::compact().print_pattern(&pattern);
        assert_eq!(printed, expected);
        assert_eq!(parse_pattern(&printed).unwrap(), pattern, "{printed}");
        assert_eq!(back.convert(&pattern).unwrap(), term, "{printed}");
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
        production: Some(catalog.identity(production)),
        sort: None,
        origin: None,
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
    let stale = catalog.productions_for(&LabelHead::new("b"))[0];
    let stale_application = Term::apply("a", Vec::new()).with_metadata(TermMetadata {
        span: None,
        production: Some(catalog.identity(stale)),
        sort: None,
        origin: None,
    });
    let term = Term::Rewrite {
        left: Box::new(stale_application),
        right: Box::new(Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("A")),
        }),
    };

    assert_eq!(
        Printer::compact().print_pattern(
            &TermConverter::new(&resolved, "MAIN")
                .unwrap()
                .convert(&term)
                .expect("the unique visible production should replace the stale identity")
        ),
        "\\rewrites{SortA{}}(Lbla{}(), VarX:SortA{})"
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
    let stale = catalog.productions_for(&LabelHead::new("stale"))[0];
    let choice = Term::apply("choice", Vec::new()).with_metadata(TermMetadata {
        span: None,
        production: Some(catalog.identity(stale)),
        sort: Some(Sort::new("A")),
        origin: None,
    });
    let term = Term::Rewrite {
        left: Box::new(choice),
        right: Box::new(Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("A")),
        }),
    };

    assert_eq!(
        Printer::compact().print_pattern(
            &TermConverter::new(&resolved, "MAIN")
                .unwrap()
                .convert(&term)
                .expect("the metadata sort should replace the stale identity")
        ),
        "\\rewrites{SortA{}}(Lblchoice{}(), VarX:SortA{})"
    );
}

#[test]
fn rejects_an_unbound_sentence_sort_variable_in_a_term() {
    let sort = Sort::with_parameters("#SortParam", vec![Sort::new("Q0")]);
    let term = Term::Apply {
        label: Label::with_parameters("#Top", vec![sort.clone()]),
        arguments: Vec::new(),
    };
    let error = convert_handbuilt(&term).unwrap_err();
    assert_eq!(
        error.to_string(),
        "the sentence sort variable #SortParam{Q0} is not bound by the sentence being converted"
    );
}

#[test]
fn rejects_unbound_sentence_sort_variables_on_every_sort_conversion_path() {
    let definition = lowered("module MAIN\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let converter = TermConverter::new(&resolved, "MAIN").unwrap();
    let variable = Sort::with_parameters("#SortParam", vec![Sort::new("Q0")]);
    for sort in [
        variable.clone(),
        Sort::with_parameters("MInt", vec![variable.clone()]),
    ] {
        let expected = TermConversionError::UnboundSortVariable {
            sort: variable.clone(),
        };
        assert_eq!(converter.convert_sort(&sort).unwrap_err(), expected);
        assert_eq!(
            converter
                .convert_label(&Label::with_parameters("f", vec![sort.clone()]))
                .unwrap_err(),
            expected
        );
        let terms = [
            Term::Variable {
                name: "X".into(),
                sort: Some(sort.clone()),
            },
            Term::Apply {
                label: Label::with_parameters("f", vec![sort.clone()]),
                arguments: Vec::new(),
            },
            Term::Apply {
                label: Label::with_parameters("#AG", vec![sort.clone()]),
                arguments: Vec::new(),
            },
            Term::Apply {
                label: Label::with_parameters("#Exists", vec![Sort::new("Int")]),
                arguments: vec![
                    Term::Variable {
                        name: "X".into(),
                        sort: Some(sort),
                    },
                    Term::apply("f", Vec::new()),
                ],
            },
        ];
        for term in terms {
            assert_eq!(converter.convert(&term).unwrap_err(), expected, "{term}");
        }
    }
}

#[test]
fn rejects_malformed_sentence_sort_variables() {
    let definition = lowered("module MAIN\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let converter = TermConverter::new(&resolved, "MAIN").unwrap();
    for sort in [
        Sort::new("#SortParam"),
        Sort::with_parameters("#SortParam", vec![Sort::new("Q0"), Sort::new("Q1")]),
        Sort::with_parameters(
            "#SortParam",
            vec![Sort::with_parameters("Q0", vec![Sort::new("Int")])],
        ),
    ] {
        let term = Term::Variable {
            name: "X".into(),
            sort: Some(sort.clone()),
        };
        let expected = TermConversionError::UnboundSortVariable { sort: sort.clone() };
        assert_eq!(converter.convert(&term).unwrap_err(), expected);
        assert_eq!(converter.convert_sort(&sort).unwrap_err(), expected);
        assert_eq!(
            converter
                .convert_label(&Label::with_parameters("f", vec![sort]))
                .unwrap_err(),
            expected
        );
    }
}
