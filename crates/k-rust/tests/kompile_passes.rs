use indoc::indoc;
use k_rust::{
    definition::{
        Attributes, Definition, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::{Label, Sort, Term, printer::Printer},
    kompile::{
        module_to_kore, resolve_comm, resolve_config_var, resolve_fun,
        resolve_function_with_config, resolve_io,
    },
    outer::{ResolvedSource, load},
};
use serde_json::{Value, json};
use std::collections::BTreeMap;

fn parsed(source: &str) -> k_rust::definition::Definition {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    load(
        ResolvedSource::new("definition.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap()
    .definition
}

#[test]
fn duplicates_commutative_simplification_rules_and_removes_rule_comm() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= Exp "+" Exp [comm, function, symbol(_+_)]
          rule X:Exp + Y:Exp => Y:Exp + X:Exp [simplification, comm, label(commute)]
        endmodule
    "#};
    let definition = resolve_comm(&parsed(source)).unwrap();
    let printer = Printer::new();
    let rules = definition.modules[0]
        .local_sentences
        .iter()
        .filter_map(|sentence| {
            let Sentence::Rule {
                body, attributes, ..
            } = sentence
            else {
                return None;
            };
            Some((printer.print_term(body), attributes.entries()))
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
}

#[test]
fn rejects_rule_comm_when_the_lhs_symbol_is_not_commutative() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= Exp "+" Exp [function, symbol(_+_)]
          rule X:Exp + Y:Exp => X:Exp [simplification, comm]
        endmodule
    "#};
    let error = resolve_comm(&parsed(source)).unwrap_err();

    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Used 'comm' attribute on simplification rule but _+_ is not comm."
    );
}

fn attributes(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn application(label: &str, arguments: Vec<Term>) -> Term {
    Term::Apply {
        label: Label::new(label),
        arguments,
    }
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn rule(body: Term, attributes: Attributes) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes,
    }
}

fn production(label: &str, sort: &str, attributes: Attributes) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(label)),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: Vec::new(),
        attributes,
    }
}

fn module(name: &str, sentences: Vec<Sentence>) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: Vec::new(),
        local_sentences: sentences,
        attributes: Attributes::default(),
    }
}

fn incomplete_cell(label: &str, body: Term) -> Term {
    application(
        label,
        vec![
            application("#noDots", Vec::new()),
            body,
            application("#dots", Vec::new()),
        ],
    )
}

fn io_fixture(stream: &str) -> Definition {
    let builtin_init = rule(
        rewrite(
            application("initStdinCell", vec![Term::variable("Init")]),
            incomplete_cell(
                "<stdin>",
                application("builtinInput", vec![Term::variable("Init")]),
            ),
        ),
        attributes(&[("initializer", json!(""))]),
    );
    let unblock = rule(
        incomplete_cell(
            "<stdin>",
            rewrite(
                application(".List", Vec::new()),
                application(
                    "ListItem",
                    vec![application(
                        "#parseInput",
                        vec![
                            application("#SemanticCastToString", vec![Term::variable("?Sort")]),
                            application(
                                "#SemanticCastToString",
                                vec![Term::variable("?Delimiters")],
                            ),
                        ],
                    )],
                ),
            ),
        ),
        attributes(&[("label", json!("STDIN-STREAM.stdinUnblock"))]),
    );
    let stream_rule = rule(
        incomplete_cell("<stdin>", application("builtinStep", Vec::new())),
        attributes(&[("stream", json!(""))]),
    );
    let stdin = module(
        "STDIN-STREAM",
        vec![
            builtin_init,
            unblock,
            stream_rule,
            production("#buffer", "Stream", Attributes::default()),
        ],
    );

    let user_init = rule(
        rewrite(
            application("initInCell", vec![Term::variable("Init")]),
            incomplete_cell("<in>", application("oldInput", Vec::new())),
        ),
        attributes(&[("initializer", json!(""))]),
    );
    let consume = rule(
        incomplete_cell(
            "<in>",
            rewrite(
                application(
                    "ListItem",
                    vec![application(
                        "#SemanticCastToInt",
                        vec![Term::variable("Value")],
                    )],
                ),
                application(".List", Vec::new()),
            ),
        ),
        attributes(&[("label", json!("consume"))]),
    );
    let main = module(
        "MAIN",
        vec![
            production("<in>", "InCell", attributes(&[("stream", json!(stream))])),
            user_init,
            consume,
        ],
    );
    Definition {
        main_module: "MAIN".into(),
        modules: vec![
            main,
            stdin,
            module("STDOUT-STREAM", Vec::new()),
            module("K-IO", Vec::new()),
            module("K-REFLECTION", Vec::new()),
        ],
        attributes: Attributes::default(),
    }
}

#[test]
fn resolves_stream_initializers_unblocking_rules_and_builtin_sentences() {
    let definition = resolve_io(&io_fixture("stdin")).unwrap();
    let main = definition.main_module().unwrap();
    let rendered = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(main.imports.iter().any(|import| import.name == "K-IO"));
    assert!(
        main.imports
            .iter()
            .any(|import| import.name == "K-REFLECTION")
    );
    assert!(rendered.iter().any(|body| {
        body.contains("initInCell") && body.contains("builtinInput") && !body.contains("oldInput")
    }));
    assert!(rendered.iter().any(|body| {
        body.contains("#parseInput")
            && body.contains("#token(\"\\\"Int\\\"\",\"String\")")
            && body.contains("`<in>`")
    }));
    assert!(
        rendered
            .iter()
            .any(|body| body.contains("builtinStep") && body.contains("`<in>`"))
    );
    assert!(main.local_sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Production { sort, .. } if sort.name == "Stream")
    }));
    for template in ["STDIN-STREAM", "STDOUT-STREAM"] {
        let module = definition
            .modules
            .iter()
            .find(|module| module.name == template)
            .unwrap();
        assert!(module.imports.is_empty());
        assert!(module.local_sentences.is_empty());
    }
}

#[test]
fn rejects_unknown_stream_names() {
    let error = resolve_io(&io_fixture("stderr")).unwrap_err();

    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Make sure you give the correct stream names: stderr\nIt should be one of [stdin, stdout]"
    );
}

#[test]
fn lowers_local_functions_with_closure_arguments_and_totality() {
    let x = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Int")),
    };
    let y = Term::Variable {
        name: "Y".into(),
        sort: Some(Sort::new("Int")),
    };
    let local_function = application(
        "#fun3",
        vec![
            x.clone(),
            application("plus", vec![x, y.clone()]),
            Term::Token {
                token: "1".into(),
                sort: Sort::new("Int"),
            },
        ],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("plus")),
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    items: vec![
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Int"),
                            name: None,
                        },
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Int"),
                            name: None,
                        },
                    ],
                    attributes: Attributes::default(),
                },
                rule(local_function, Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    let lambda = sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } if label.name.starts_with("#lambda") => {
                Some((label.clone(), items.clone(), attributes.clone()))
            }
            _ => None,
        })
        .expect("lambda production should be generated");
    assert_eq!(lambda.0.name, "#lambda__");
    assert_eq!(
        lambda
            .1
            .iter()
            .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
            .count(),
        2,
        "the argument and captured Y should be explicit parameters"
    );
    assert!(lambda.2.get("function").is_some());
    assert!(lambda.2.get("total").is_some());

    let rendered = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered
            .iter()
            .any(|body| body.contains("`#lambda__`(#token(\"1\",\"Int\"),Y)")),
        "{rendered:#?}"
    );
    assert!(
        rendered
            .iter()
            .any(|body| { body.contains("`#lambda__`(X,Y)=>plus(X,Y)") })
    );
}

#[test]
fn lowers_k_non_matching_to_a_negated_predicate_with_owise_rule() {
    let pattern = rewrite(
        Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("Int")),
        },
        bool_token_for_test(true),
    );
    let expression = Term::Token {
        token: "0".into(),
        sort: Sort::new("Int"),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: Attributes::default(),
                },
                rule(
                    application("_:/=K_", vec![pattern, expression]),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    assert!(sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Rule { attributes, .. } if attributes.get("owise").is_some())
    }));
    let rendered = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered
            .iter()
            .any(|body| { body.contains("`notBool_`(`#lambda") }),
        "{rendered:#?}"
    );
}

fn bool_token_for_test(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

#[test]
fn rebases_parser_metadata_after_generating_lambda_productions() {
    let source = indoc! {r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "f(" Int ")" [function, symbol(f)]
          syntax Int ::= "#fun" "(" Int "=>" Int ")" "(" Int ")" [symbol(#fun3)]
          rule f(X:Int) => #fun(Y:Int => Y:Int)(X:Int)
        endmodule
    "##};
    let transformed = resolve_fun(&parsed(source)).unwrap();

    module_to_kore(&transformed, "MAIN")
        .expect("surviving parser production metadata should use the expanded catalog");
}

#[test]
fn threads_configuration_through_transitive_function_calls() {
    let function = attributes(&[("function", json!(""))]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("reader", "Int", function.clone()),
                production("caller", "Int", function),
                production("plain", "Int", Attributes::default()),
                rule(
                    rewrite(
                        application("reader", Vec::new()),
                        Term::Variable {
                            name: "!Fresh".into(),
                            sort: Some(Sort::new("Int")),
                        },
                    ),
                    Attributes::default(),
                ),
                rule(
                    rewrite(
                        application("caller", Vec::new()),
                        application("reader", Vec::new()),
                    ),
                    Attributes::default(),
                ),
                rule(
                    rewrite(
                        application("plain", Vec::new()),
                        application("caller", Vec::new()),
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_function_with_config(&definition).unwrap();
    let main = transformed.main_module().unwrap();
    let production_arities = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } => Some((label.name.as_str(), items.len())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(production_arities["reader"], 1);
    assert_eq!(production_arities["caller"], 1);
    assert_eq!(production_arities["plain"], 0);

    let rendered = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered
            .iter()
            .any(|body| body.contains("caller(#Configuration)=>reader(#Configuration)")),
        "{rendered:#?}"
    );
    assert!(
        rendered
            .iter()
            .any(|body| body == "plain(.KList)=>caller(#Configuration)"),
        "{rendered:#?}"
    );
}

#[test]
fn lowers_with_config_rules_to_a_top_cell_alias() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("f", "Int", attributes(&[("function", json!(""))])),
                rule(
                    application(
                        "#withConfig",
                        vec![
                            rewrite(application("f", Vec::new()), truth()),
                            incomplete_cell("<k>", Term::variable("K")),
                        ],
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_function_with_config(&definition).unwrap();
    let rendered = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();
    assert!(rendered.starts_with("f(`<generatedTop>`("), "{rendered}");
    assert!(rendered.contains("#dots(.KList),"), "{rendered}");
    assert!(rendered.contains(" #as #Configuration"), "{rendered}");
    assert!(rendered.contains("#Configuration"), "{rendered}");
    assert!(
        rendered.ends_with(")=>#token(\"true\",\"Bool\")"),
        "{rendered}"
    );
}

#[test]
fn rebases_function_metadata_after_adding_configuration_arguments() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "f(" Int ")" [function, symbol(f)]
          rule f(X:Int) => !Y:Int
        endmodule
    "#};
    let transformed = resolve_function_with_config(&parsed(source)).unwrap();
    let resolved = ResolvedDefinition::resolve(&transformed).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let productions = resolved.production_catalog(module);
    let rule = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let Term::Rewrite { left, .. } = rule.unannotated() else {
        panic!("parsed rule should contain a rewrite")
    };
    let Term::Apply { label, arguments } = left.unannotated() else {
        panic!("parsed rule lhs should be an application")
    };
    assert_eq!(label.name, "f");
    assert_eq!(arguments.len(), 2);
    let production = left
        .metadata()
        .and_then(|metadata| metadata.production)
        .map(|id| productions.production(k_rust::definition::ProductionId(id.0)))
        .expect("parsed application should retain transformed production identity");
    assert!(matches!(
        production,
        Sentence::Production { items, .. }
            if matches!(items.last(), Some(ProductionItem::NonTerminal { sort, .. })
                if sort.name == "GeneratedTopCell")
    ));
}

#[test]
fn aliases_a_rewritten_top_cell_when_configuration_is_used() {
    let top = application(
        "<generatedTop>",
        vec![application("<k>", vec![Term::variable("K")])],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::Rule {
                body: rewrite(top.clone(), top),
                requires: application("needs", vec![Term::variable("#Configuration")]),
                ensures: truth(),
                attributes: Attributes::default(),
            }],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_config_var(&definition);
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert!(matches!(
        body.unannotated(),
        Term::Rewrite { left, .. }
            if matches!(left.unannotated(), Term::As { alias, .. }
                if matches!(alias.unannotated(), Term::Variable { name, .. }
                    if name == "#Configuration"))
    ));
}

#[test]
fn does_not_alias_a_top_cell_for_unresolved_fresh_variables_alone() {
    let top = application(
        "<generatedTop>",
        vec![application("<k>", vec![Term::variable("K")])],
    );
    let original = rewrite(top.clone(), top);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::Rule {
                body: original.clone(),
                requires: application("needs", vec![Term::variable("!Fresh")]),
                ensures: truth(),
                attributes: Attributes::default(),
            }],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_config_var(&definition);
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert_eq!(body, &original);
}
