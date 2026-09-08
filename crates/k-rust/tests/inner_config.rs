use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use k_rust::inner::{ConfigError, resolve_configuration_bubbles};
use k_rust::kast::{Label, Sort};
use proptest::prelude::*;

macro_rules! assert_config_snapshot {
    ($source:expr, $value:expr) => {{
        let source = $source;
        let value = &$value;
        insta::with_settings!({
            description => format!("Configuration bubble:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(value);
        });
    }};
}

fn definition(contents: &str) -> Definition {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: vec![],
            local_sentences: vec![
                Sentence::Production {
                    label: None,
                    parameters: vec![],
                    sort: Sort::new("Int"),
                    items: vec![ProductionItem::regex("[0-9]+")],
                    attributes: token_attributes,
                },
                Sentence::Bubble {
                    sentence_type: "config".into(),
                    contents: contents.into(),
                    attributes: Attributes::default(),
                },
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

#[test]
fn parses_nested_cells_properties_casts_and_ensures() {
    let source =
        r#"<top multiplicity="1"><k> $PGM:Int </k><counter> 0 </counter></top> ensures true"#;
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(source, transformed);
    assert!(matches!(
        transformed.main_module().unwrap().local_sentences[1],
        Sentence::Configuration { .. }
    ));
}

#[test]
fn bare_configuration_variable_is_cast_to_its_inferred_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module CONFIG-VAR-CAST --syntax-module CONFIG-VAR-CAST --output-definition ref (exit 0)
    // parsed.txt: rule initKCell(_0)=>`<k>`(#noDots(.KList),#SemanticCastToK(`project:KItem`(`Map:lookup`(_0,#token("$PGM","KConfigVar")))),#noDots(.KList)) ...
    // A KConfigVar constant is a variable to both reference inference engines
    // (SortInferencer.java:228 and :563, TypeInferenceVisitor.java:221-233), so the bare `$PGM`
    // under `<k>` is cast to its inferred sort K before configuration generation reads it.
    let source = "<k> $PGM </k>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();
    let Sentence::Configuration { body, .. } =
        &transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("the bubble should resolve to a configuration");
    };

    assert_eq!(
        body.to_string(),
        "#configCell(#token(\"k\",\"#CellName\"),#cellPropertyListTerminator(.KList),#SemanticCastToK(#token(\"$PGM\",\"KConfigVar\")),#token(\"k\",\"#CellName\"))"
    );
}

#[test]
fn explicitly_cast_configuration_variable_keeps_its_single_cast() {
    // Control for the inferred cast: `$PGM:Int` already carries its cast and must not be wrapped
    // again (SortInferencer.insertCasts skips a constant under an existing cast).
    let source = "<k> $PGM:Int </k>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();
    let Sentence::Configuration { body, .. } =
        &transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("the bubble should resolve to a configuration");
    };

    assert_eq!(
        body.to_string(),
        "#configCell(#token(\"k\",\"#CellName\"),#cellPropertyListTerminator(.KList),#SemanticCastToInt(#token(\"$PGM\",\"KConfigVar\")),#token(\"k\",\"#CellName\"))"
    );
}

#[test]
fn declared_kconfigvar_does_not_create_a_reflexive_subsort_bridge() {
    let mut input = definition("<k> $PGM:Int </k>");
    input.modules[0].local_sentences.insert(
        0,
        Sentence::SyntaxSort {
            parameters: vec![],
            sort: Sort::new("KConfigVar"),
            attributes: Attributes::default(),
        },
    );

    resolve_configuration_bubbles(&input).unwrap();
}

#[test]
fn preserves_external_cells() {
    let transformed = resolve_configuration_bubbles(&definition("<shared/>")).unwrap();
    let Sentence::Configuration { body, .. } =
        &transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("expected configuration")
    };
    assert!(matches!(
        body.unannotated(),
        k_rust::kast::Term::Apply { label, arguments }
            if label == &Label::new("#externalCell") && arguments.len() == 1
    ));
}

#[test]
fn parses_chained_casts_and_empty_bags() {
    let source = "<top><k> $PGM:Int:K </k><cells> .Bag </cells></top>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[1]
    );
}

fn synonym_configuration(contents: &str, import_aliases: bool) -> Definition {
    let source = format!(
        r#"
        module ALIASES
          syntax Wad = Rat
          syntax Ray = Rat
        endmodule
        module MAIN
          {}
          syntax Rat ::= r"[0-9]+" [token]
          syntax Other ::= "other" [symbol(other)]
          configuration <r> {contents} </r>
        endmodule
        "#,
        if import_aliases {
            "imports ALIASES"
        } else {
            ""
        },
    );
    let parsed = k_rust::outer::parse("synonym.k", &source).unwrap();
    k_rust::definition::apply_sort_synonyms(&k_rust::outer::lower(&parsed, "MAIN").unwrap())
        .unwrap()
}

#[test]
fn configuration_synonym_casts_use_the_target_sort() {
    // The synonym corpus's 0:Wad needs only an unambiguous token grammar.
    // Both aliases must produce the same semantic cast as their canonical sort.
    for contents in ["0:Rat", "0:Wad", "0:Ray", "0:Wad:Ray"] {
        let transformed = resolve_configuration_bubbles(&synonym_configuration(contents, true))
            .unwrap_or_else(|error| panic!("{contents}: {error}"));
        let body = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Configuration { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        let token = "#token(\"0\",\"Rat\")";
        let mut value = format!("#SemanticCastToRat({token})");
        if contents == "0:Wad:Ray" {
            value = format!("#SemanticCastToRat({value})");
        }
        assert_eq!(
            body.to_string(),
            format!(
                "#configCell(#token(\"r\",\"#CellName\"),#cellPropertyListTerminator(.KList),{value},#token(\"r\",\"#CellName\"))"
            ),
            "{contents}"
        );
    }
}

#[test]
fn configuration_synonym_casts_reject_incompatible_values_and_hidden_aliases() {
    for (contents, imported) in [
        ("other:Rat", true),
        ("other:Wad", true),
        ("0:Other", true),
        ("0:Wad", false),
    ] {
        let result = resolve_configuration_bubbles(&synonym_configuration(contents, imported));
        assert!(
            matches!(
                result,
                Err(ConfigError::Parse { ref error, .. })
                    if matches!(error.as_ref(), k_rust::inner::ParseError::NoParse { .. })
            ),
            "{contents} (imported={imported}) must be rejected: {result:?}"
        );
    }
}

#[test]
fn parses_k_sequences_in_configuration_cells() {
    let source = "<k> foo ~> $PGM:Int </k>";
    let mut input = definition(source);
    input.modules[0].local_sentences.insert(
        1,
        Sentence::Production {
            label: Some(Label::new("foo")),
            parameters: vec![],
            sort: Sort::new("Foo"),
            items: vec![ProductionItem::Terminal("foo".into())],
            attributes: Attributes::default(),
        },
    );
    let transformed = resolve_configuration_bubbles(&input).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[2]
    );
}

#[test]
fn parses_record_productions_in_configurations() {
    let source = "<k> pair(... left: 1) </k>";
    let mut input = definition(source);
    input.modules[0].local_sentences.insert(
        1,
        Sentence::Production {
            label: Some(Label::new("pair")),
            parameters: vec![],
            sort: Sort::new("Pair"),
            items: vec![
                ProductionItem::Terminal("pair".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: Some("left".into()),
                },
                ProductionItem::Terminal(",".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: Some("right".into()),
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: Attributes::default(),
        },
    );
    let transformed = resolve_configuration_bubbles(&input).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[2]
    );
}

#[test]
fn parses_literal_cell_names_that_are_also_user_terminals() {
    let source = "<value> .K </value>";
    let mut input = definition(source);
    input.modules[0].local_sentences.insert(
        1,
        Sentence::Production {
            label: Some(Label::new("value")),
            parameters: vec![],
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::Terminal("value".into())],
            attributes: Attributes::default(),
        },
    );
    let transformed = resolve_configuration_bubbles(&input).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[2]
    );
}

#[test]
fn parses_uppercase_cell_names_without_treating_them_as_variables() {
    let source = "<T><k> $PGM:Int </k></T>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[1]
    );
}

#[test]
fn rejects_requires_clauses_after_parsing_them() {
    assert!(matches!(
        resolve_configuration_bubbles(&definition("<k> 0 </k> requires true")),
        Err(ConfigError::IllegalRequires { module, .. }) if module == "MAIN"
    ));
}

#[test]
fn configuration_grammar_includes_imported_productions() {
    let mut input = definition("<k> zero </k>");
    input.modules.insert(
        0,
        FlatModule {
            name: "BASE".into(),
            imports: vec![],
            local_sentences: vec![Sentence::Production {
                label: Some(Label::new("zero")),
                parameters: vec![],
                sort: Sort::new("Exp"),
                items: vec![ProductionItem::Terminal("zero".into())],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        },
    );
    input.modules[1]
        .imports
        .push(k_rust::definition::FlatImport {
            name: "BASE".into(),
            public: true,
        });

    let transformed = resolve_configuration_bubbles(&input).unwrap();
    let Sentence::Configuration { body, .. } =
        &transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("expected configuration")
    };
    let mut labels = Vec::new();
    body.visit_preorder(&mut |term| {
        if let k_rust::kast::Term::Apply { label, .. } = term {
            labels.push(label.name.clone());
        }
    });
    assert!(labels.contains(&"zero".to_owned()));
}

#[test]
fn configuration_grammar_uses_the_module_signature() {
    let mut input = definition("<k> foo </k>");
    let foo = Sentence::Production {
        label: Some(Label::new("foo")),
        parameters: vec![],
        sort: Sort::new("Foo"),
        items: vec![ProductionItem::Terminal("foo".into())],
        attributes: Attributes::default(),
    };
    let mut private_attributes = Attributes::default();
    private_attributes.insert("private", serde_json::json!(""));
    input.modules.insert(
        0,
        FlatModule {
            name: "BASE".into(),
            imports: vec![],
            local_sentences: vec![foo],
            attributes: Attributes::default(),
        },
    );
    input.modules.insert(
        1,
        FlatModule {
            name: "MID".into(),
            imports: vec![FlatImport {
                name: "BASE".into(),
                public: false,
            }],
            local_sentences: vec![],
            attributes: private_attributes,
        },
    );
    input.modules[2].imports.push(FlatImport {
        name: "MID".into(),
        public: true,
    });

    let hidden = resolve_configuration_bubbles(&input);
    assert!(
        matches!(
            hidden,
            Err(ConfigError::Parse { ref error, .. })
                if matches!(error.as_ref(), k_rust::inner::ParseError::NoParse { .. })
        ),
        "{hidden:?}"
    );

    input.modules[1].imports[0].public = true;
    resolve_configuration_bubbles(&input)
        .expect("an explicitly public import remains in the configuration signature");
}

proptest! {
    #[test]
    fn arbitrary_configuration_bubbles_never_panic(contents in any::<String>()) {
        let _ = resolve_configuration_bubbles(&definition(&contents));
    }
}

#[cfg(feature = "z3-inference")]
#[test]
fn configuration_brackets_preserve_sequence_order_and_scope() {
    for contents in ["(1 ~> 2)", "(1 ~> 2) ~> 3", "1 ~> (2 ~> 3)", "((1)) ~> 2"] {
        let input = definition(&format!("<k> {contents} </k>"));
        let transformed = resolve_configuration_bubbles(&input)
            .expect("the implicit configuration grammar includes KSEQ brackets");
        let Sentence::Configuration { body, .. } =
            &transformed.main_module().unwrap().local_sentences[1]
        else {
            panic!("expected a configuration");
        };
        let mut sequence = Vec::new();
        body.visit_preorder(&mut |term| {
            if let k_rust::kast::Term::Token { token, sort } = term {
                if sort.name == "Int" {
                    sequence.push(token.clone());
                }
            }
        });
        let expected = if contents.contains('3') {
            vec!["1", "2", "3"]
        } else {
            vec!["1", "2"]
        };
        assert_eq!(sequence, expected);
    }
    for malformed in ["(1 ~> 2", "1 ~> 2)", "(1 ~> )"] {
        assert!(
            resolve_configuration_bubbles(&definition(&format!("<k> {malformed} </k>"))).is_err()
        );
    }
}

#[cfg(not(feature = "z3-inference"))]
#[test]
fn portable_configuration_brackets_report_ambiguous_inference_boundary() {
    let error = resolve_configuration_bubbles(&definition("<k> ((1)) ~> 2 </k>")).unwrap_err();
    assert!(matches!(error, ConfigError::Parse { error, .. }
        if matches!(*error, k_rust::inner::ParseError::Z3InferenceRequired { ambiguity: true, .. })));
}

#[test]
fn configuration_sequence_seed_preserves_declared_left_associativity() {
    let mut input = definition("<k> 1 ~> 2 ~> 3 </k>");
    input.modules[0].local_sentences.push(Sentence::SyntaxAssociativity {
        associativity: k_rust::definition::Associativity::Left,
        tags: vec!["#KSequence".into()],
        attributes: Attributes::default(),
    });
    let transformed = resolve_configuration_bubbles(&input)
        .expect("the KSEQ declaration and implicit seed must not prohibit both associations");
    let Sentence::Configuration { body, .. } = &transformed.main_module().unwrap().local_sentences[1] else {
        panic!("expected a configuration");
    };
    let mut values = Vec::new();
    body.visit_preorder(&mut |term| {
        if let k_rust::kast::Term::Token { token, sort } = term {
            if sort.name == "Int" { values.push(token.clone()); }
        }
    });
    assert_eq!(values, ["1", "2", "3"]);
}
