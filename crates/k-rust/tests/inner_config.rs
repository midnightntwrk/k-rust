use std::sync::Arc;

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use k_rust::inner::{ConfigError, NoParseInput, ParseError, resolve_configuration_bubbles};
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
                }
                .into(),
                Sentence::Bubble {
                    sentence_type: "config".into(),
                    contents: contents.into(),
                    attributes: Attributes::default(),
                }
                .into(),
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

#[test]
fn schematic_configuration_leaf_cast_preserves_metadata_and_nested_applications() {
    use k_rust::kast::Term;

    let source = r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= wrap(S) [function]
          configuration <top><foo> wrap(wrap(0)) </foo><bar> wrap(1) </bar></top>
        endmodule
    "#;
    let parsed = k_rust::outer::parse("schematic-configuration.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let transformed = resolve_configuration_bubbles(&lowered).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Configuration { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();

    let mut casts = 0;
    let mut saw_nested_wrap = false;
    body.visit_preorder(&mut |term| {
        let Term::Apply { label, arguments } = term.unannotated() else {
            return;
        };
        assert!(
            label.parameters.is_empty(),
            "parsed configurations erase inferred label parameters: {label}"
        );
        if label.semantic_cast_sort() != Some(Sort::new("K")) {
            return;
        }
        casts += 1;
        assert_eq!(arguments.len(), 1);
        let leaf = &arguments[0];
        let Term::Apply {
            label: leaf_label,
            arguments: leaf_arguments,
        } = leaf.unannotated()
        else {
            panic!("the inferred cast encloses the original application");
        };
        assert!(leaf_label.name.starts_with("wrap("), "{leaf_label}");
        let metadata = leaf.metadata().expect("the parsed leaf keeps its metadata");
        assert!(metadata.production.is_some());
        let span = metadata
            .span
            .expect("the parsed leaf keeps its source span");
        let text = &source[span.start..span.end];
        assert!(matches!(text, "wrap(wrap(0))" | "wrap(1)"), "{text}");
        if text == "wrap(wrap(0))" {
            assert!(matches!(
                leaf_arguments[0].unannotated(),
                Term::Apply { label, .. } if label.name == leaf_label.name
            ));
            saw_nested_wrap = true;
        }
    });
    assert_eq!(casts, 2, "only the two cell-content leaves need casts");
    assert!(
        saw_nested_wrap,
        "the nested argument keeps its original application"
    );
}

#[test]
fn explicitly_cast_schematic_configuration_leaf_keeps_one_cast() {
    use k_rust::kast::Term;

    let source = r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= wrap(S) [function]
          configuration <foo> (wrap(0)):Int </foo>
        endmodule
    "#;
    let parsed = k_rust::outer::parse("schematic-cast.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let transformed = resolve_configuration_bubbles(&lowered).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Configuration { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let mut casts = 0;
    body.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated() {
            casts += usize::from(label.semantic_cast_sort() == Some(Sort::new("Int")));
        }
    });
    assert_eq!(
        casts, 1,
        "the user-written cast already fixes the content sort"
    );
}

#[test]
fn parses_nested_cells_properties_casts_and_ensures() {
    let source =
        r#"<top multiplicity="1"><k> $PGM:Int </k><counter> 0 </counter></top> ensures true"#;
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(source, transformed);
    assert!(matches!(
        *transformed.main_module().unwrap().local_sentences[1],
        Sentence::Configuration { .. }
    ));
}

#[test]
fn configuration_errors_do_not_fabricate_missing_provenance() {
    let error = resolve_configuration_bubbles(&definition("@@@"))
        .expect_err("the configuration is not recognized");
    assert!(matches!(
        error,
        ConfigError::Parse {
            source: None,
            location: None,
            error,
            ..
        } if matches!(
            error.as_ref(),
            ParseError::NoParse {
                input: NoParseInput::UnrecognizedInput { value },
                previous: None,
                span: None,
                ..
            } if value == "@"
        )
    ));
}

#[test]
fn bare_configuration_variable_is_cast_to_its_inferred_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module CONFIG-VAR-CAST --syntax-module CONFIG-VAR-CAST --output-definition ref (exit 0)
    // parsed.txt: rule initKCell(_0)=>`<k>`(#noDots(.KList),#SemanticCastToK(`project:KItem`(`Map:lookup`(_0,#token("$PGM","KConfigVar")))),#noDots(.KList)) ...
    // A KConfigVar constant stands for the value supplied for it when the configuration is
    // initialized, so sort inference types it as a variable, and the bare `$PGM` under `<k>` is
    // cast to its inferred sort K before configuration generation reads it.
    let source = "<k> $PGM </k>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();
    let Sentence::Configuration { body, .. } =
        &*transformed.main_module().unwrap().local_sentences[1]
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
    // again: the explicit cast already fixes the sort an inferred cast would record.
    let source = "<k> $PGM:Int </k>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();
    let Sentence::Configuration { body, .. } =
        &*transformed.main_module().unwrap().local_sentences[1]
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
        Arc::new(Sentence::SyntaxSort {
            parameters: vec![],
            sort: Sort::new("KConfigVar"),
            attributes: Attributes::default(),
        }),
    );

    resolve_configuration_bubbles(&input).unwrap();
}

#[test]
fn preserves_external_cells() {
    let transformed = resolve_configuration_bubbles(&definition("<shared/>")).unwrap();
    let Sentence::Configuration { body, .. } =
        &*transformed.main_module().unwrap().local_sentences[1]
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
            .find_map(|sentence| match &**sentence {
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
fn configuration_casts_through_a_synonym_chain_use_the_end_of_the_chain() {
    let source = r#"
        module ALIASES
          syntax Ray = Rat
          syntax Wad = Ray
        endmodule
        module MAIN
          imports ALIASES
          syntax Rat ::= r"[0-9]+" [token]
          configuration <r> 0:Wad </r>
        endmodule
        "#;
    let parsed = k_rust::outer::parse("synonym-chain.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let applied = k_rust::definition::apply_sort_synonyms(&lowered).unwrap();
    let transformed = resolve_configuration_bubbles(&applied).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Configuration { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        body.to_string(),
        "#configCell(#token(\"r\",\"#CellName\"),#cellPropertyListTerminator(.KList),#SemanticCastToRat(#token(\"0\",\"Rat\")),#token(\"r\",\"#CellName\"))"
    );
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
        Arc::new(Sentence::Production {
            label: Some(Label::new("foo")),
            parameters: vec![],
            sort: Sort::new("Foo"),
            items: vec![ProductionItem::Terminal("foo".into())],
            attributes: Attributes::default(),
        }),
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
        Arc::new(Sentence::Production {
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
        }),
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
        Arc::new(Sentence::Production {
            label: Some(Label::new("value")),
            parameters: vec![],
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::Terminal("value".into())],
            attributes: Attributes::default(),
        }),
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

fn resolve_source(source: &str, main_module: &str) -> Result<Definition, ConfigError> {
    let parsed = k_rust::outer::parse("phrase-token-configuration.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, main_module).unwrap();
    resolve_configuration_bubbles(&lowered)
}

/// Syntax in which `Toks ::= Names [token]` is a token of a phrase's text. `Names` is program
/// text only: a configuration variable reaching `Toks` by unary productions alone is no phrase
/// of it, and is read as the variable.
const PHRASE_TOKEN_SYNTAX: &str = r#"
module T-SYNTAX
  syntax Name ::= r"[a-z]+" [token]
  syntax Names ::= List{Name, ","}
  syntax Toks ::= Names [token]
  syntax Pgm ::= Toks
  syntax Run ::= "run" Toks
endmodule
"#;

fn configuration_body(definition: &Definition) -> String {
    definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Configuration { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the bubble should resolve to a configuration")
}

#[test]
fn a_configuration_variable_whose_sort_reaches_a_phrase_token_is_read_as_the_variable() {
    let source = format!(
        "{PHRASE_TOKEN_SYNTAX}
module T
  imports T-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"
    );
    let body = configuration_body(&resolve_source(&source, "T").unwrap());
    assert!(
        body.contains("#SemanticCastToPgm(#token(\"$PGM\",\"KConfigVar\"))"),
        "{body}"
    );
    assert!(!body.contains("\"Toks\""), "{body}");
}

#[test]
fn a_configuration_variable_is_read_in_every_cell_at_or_above_a_phrase_token_sort() {
    let source = format!(
        "{PHRASE_TOKEN_SYNTAX}
module T
  imports T-SYNTAX
  configuration <t> <k> $PGM:Pgm </k> <x> $PGM:Toks </x> </t>
endmodule
"
    );
    let body = configuration_body(&resolve_source(&source, "T").unwrap());
    assert_eq!(
        body.matches("#token(\"$PGM\",\"KConfigVar\")").count(),
        2,
        "{body}"
    );
    assert!(!body.contains("\"Toks\""), "{body}");
}

#[test]
fn a_phrase_of_program_text_in_a_configuration_is_a_token_of_its_text() {
    // Names are digits, which no lexeme of the configuration grammar's own syntax scans.
    let source = r#"
module T
  syntax Name ::= r"[0-9]+" [token]
  syntax Names ::= List{Name, ","}
  syntax Toks ::= Names [token]
  syntax Run ::= "run" Toks
  configuration <k> run 1 , 2 </k>
endmodule
"#;
    let body = configuration_body(&resolve_source(source, "T").unwrap());
    assert!(body.contains("#token(\"1 , 2\",\"Toks\")"), "{body}");
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
            local_sentences: vec![Arc::new(Sentence::Production {
                label: Some(Label::new("zero")),
                parameters: vec![],
                sort: Sort::new("Exp"),
                items: vec![ProductionItem::Terminal("zero".into())],
                attributes: Attributes::default(),
            })],
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
        &*transformed.main_module().unwrap().local_sentences[1]
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
            local_sentences: vec![Arc::new(foo)],
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

#[test]
fn configuration_brackets_preserve_sequence_order_and_scope() {
    for contents in ["(1 ~> 2)", "(1 ~> 2) ~> 3", "1 ~> (2 ~> 3)", "((1)) ~> 2"] {
        let input = definition(&format!("<k> {contents} </k>"));
        let transformed = resolve_configuration_bubbles(&input)
            .expect("the implicit configuration grammar includes KSEQ brackets");
        let Sentence::Configuration { body, .. } =
            &*transformed.main_module().unwrap().local_sentences[1]
        else {
            panic!("expected a configuration");
        };
        let expected = if contents.contains('3') {
            vec!["1", "2", "3"]
        } else {
            vec!["1", "2"]
        };
        assert_eq!(integer_configuration_sequence(body), expected);
    }
    for malformed in ["(1 ~> 2", "1 ~> 2)", "(1 ~> )"] {
        assert!(
            resolve_configuration_bubbles(&definition(&format!("<k> {malformed} </k>"))).is_err()
        );
    }
}

#[test]
fn configuration_sequence_seed_preserves_declared_left_associativity() {
    let mut input = definition("<k> 1 ~> 2 ~> 3 </k>");
    input.modules[0]
        .local_sentences
        .push(Arc::new(Sentence::SyntaxAssociativity {
            associativity: k_rust::definition::Associativity::Left,
            tags: vec!["#KSequence".into()],
            attributes: Attributes::default(),
        }));
    let transformed = resolve_configuration_bubbles(&input)
        .expect("the KSEQ declaration and implicit seed must not prohibit both associations");
    let Sentence::Configuration { body, .. } =
        &*transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("expected a configuration");
    };
    assert_eq!(integer_configuration_sequence(body), ["1", "2", "3"]);
}

fn integer_configuration_sequence(body: &k_rust::kast::Term) -> Vec<&str> {
    use k_rust::kast::Term;
    let Term::Apply { label, arguments } = body.unannotated() else {
        panic!("expected a configuration cell");
    };
    assert_eq!(label.name, "#configCell");
    let Term::Sequence(items) = arguments[2].unannotated() else {
        panic!("expected flattened K sequence content");
    };
    items
        .iter()
        .map(|item| match item.unannotated() {
            Term::Token { token, sort } if sort.name == "Int" => token.as_str(),
            _ => panic!("unexpected sequence item: {item}"),
        })
        .collect()
}

#[test]
fn fu24_token_sort_synonym_denotes_in_configurations() {
    use k_rust::kast::Term;

    let source = r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax A = Int
          configuration <k> #token("1", "A") </k>
        endmodule
    "#;
    let parsed = k_rust::outer::parse("token-synonym.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let applied = k_rust::definition::apply_sort_synonyms(&lowered).unwrap();
    let resolved = resolve_configuration_bubbles(&applied).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Configuration { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let mut tokens = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Token { token, sort } = term.unannotated() {
            tokens.push((token.clone(), sort.clone()));
        }
    });
    assert_eq!(
        tokens,
        vec![
            ("k".into(), Sort::new("#CellName")),
            ("1".into(), Sort::new("Int")),
            ("k".into(), Sort::new("#CellName")),
        ]
    );
}
