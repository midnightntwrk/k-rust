use indoc::indoc;
use k_rust::{
    definition::{
        Attributes, Definition, FlatImport, FlatModule, LabelHead, ProductionId, ProductionItem,
        ResolvedDefinition, Sentence, check_definition,
    },
    kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata, printer::Printer},
    kompile::{
        add_cool_like_attributes, add_implicit_computation_cell, add_semantics_module,
        add_sort_injections_to_definition, check_simplification_rules, concretize_cells,
        constant_fold, expand_macros, generate_sort_predicate_rules,
        generate_sort_predicate_syntax, generate_sort_projections, guard_or_patterns,
        minimize_term_construction, module_to_kore, number_sentences, propagate_macro_attributes,
        remove_unit, resolve_anon_vars, resolve_comm, resolve_config_var, resolve_contexts,
        resolve_fresh_config_constants, resolve_fresh_constants, resolve_fun,
        resolve_function_with_config, resolve_heat_cool_attributes, resolve_io,
        resolve_semantic_casts, resolve_strict, subsort_kitem,
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
    let mut input = io_fixture("stdin");
    input
        .modules
        .iter_mut()
        .find(|module| module.name == "K-IO")
        .unwrap()
        .local_sentences
        .push(production("ioHelper", "KItem", Attributes::default()));
    let resolved = ResolvedDefinition::resolve(&input).unwrap();
    let main_id = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(main_id);
    let cell = catalog.productions_for(&LabelHead::from(&Label::new("<in>")))[0];
    let consume = input
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .iter_mut()
        .find(|sentence| sentence.attributes().get_str("label") == Some("consume"))
        .unwrap();
    let Sentence::Rule { body, .. } = consume else {
        unreachable!()
    };
    let taken = std::mem::replace(body, Term::Sequence(Vec::new()));
    *body = taken.with_metadata(TermMetadata {
        production: Some(ResolvedProductionId(cell.0)),
        ..TermMetadata::default()
    });

    let definition = resolve_io(&input).unwrap();
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
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let catalog = resolved.production_catalog(resolved.module_id("MAIN").unwrap());
    let consume = main
        .local_sentences
        .iter()
        .find(|sentence| sentence.attributes().get_str("label") == Some("consume"))
        .unwrap();
    let Sentence::Rule { body, .. } = consume else {
        unreachable!()
    };
    let rebased = body
        .metadata()
        .and_then(|metadata| metadata.production)
        .unwrap();
    assert!(matches!(
        catalog.production(ProductionId(rebased.0)),
        Sentence::Production { label: Some(label), .. } if label.name == "<in>"
    ));
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
fn local_function_variable_patterns_adopt_the_argument_sort() {
    let a = Sort::new("A");
    let b = Sort::new("B");
    let local_function = application(
        "#let",
        vec![
            Term::Variable {
                name: "X".into(),
                sort: Some(a),
            },
            Term::Token {
                token: "b".into(),
                sort: b.clone(),
            },
            Term::variable("X"),
        ],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: b.clone(),
                    attributes: Attributes::default(),
                },
                rule(local_function, Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = resolve_fun(&definition).unwrap();
    let argument_sort = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if label.name.starts_with("#lambda") => items.iter().find_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            }),
            _ => None,
        })
        .unwrap();

    assert_eq!(argument_sort, &b);
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

#[test]
fn assigns_stable_alpha_normalized_sentence_ids() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "f(" Exp ")" [symbol(f)]
          rule f(X:Exp) => X:Exp [label(first)]
          rule f(Y:Exp) => Y:Exp [label(second)]
          rule f(Z:Exp) => Z:Exp [owise, label(otherwise)]
        endmodule
    "#};
    let transformed = number_sentences(&parsed(source));
    let ids = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { attributes, .. } => Some((
                attributes.get_str("label").map(str::to_owned),
                attributes
                    .get_str("UNIQUE_ID")
                    .expect("rules are numbered")
                    .to_owned(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(ids[0].1, ids[1].1);
    assert_ne!(ids[0].1, ids[2].1);
    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(ids);
    });
}

#[test]
fn preserves_existing_sentence_ids() {
    let mut attributes = Attributes::default();
    attributes.insert("UNIQUE_ID", json!("already-numbered"));
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                rewrite(application("f", Vec::new()), truth()),
                attributes,
            )],
        )],
        attributes: Attributes::default(),
    };
    let transformed = number_sentences(&definition);
    assert_eq!(
        transformed.main_module().unwrap().local_sentences[0]
            .attributes()
            .get_str("UNIQUE_ID"),
        Some("already-numbered")
    );
}

#[test]
fn lowers_heat_and_cool_attributes_to_result_predicates() {
    let source = indoc! {r#"
        module MAIN
          syntax KResult
          syntax Exp ::= "heat" [symbol(heat)]
                       | "cool" [symbol(cool)]
          rule heat => cool [heat, result(KResult)]
          rule cool => heat [cool, result(KResult)]
        endmodule
    "#};
    let transformed = resolve_heat_cool_attributes(&parsed(source)).unwrap();
    let requires = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { requires, .. } => Some(Printer::new().print_term(requires)),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(requires);
    });
}

#[test]
fn rejects_heat_rules_without_a_result_sort_or_predicate() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                rewrite(application("heat", Vec::new()), truth()),
                attributes(&[("heat", json!("")), ("result", json!("Missing"))]),
            )],
        )],
        attributes: Attributes::default(),
    };
    let error = resolve_heat_cool_attributes(&definition).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert!(
        error.diagnostics[0]
            .message
            .starts_with("Definition is missing function isMissing required for strictness.")
    );
}

#[test]
fn removes_semantic_casts_and_retains_inferred_variable_sorts() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [symbol(f)]
          rule f(X:Exp) => X:Exp
        endmodule
    "#};
    let transformed = resolve_semantic_casts(&parsed(source));
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
    let mut variables = Vec::new();
    rule.visit_preorder(&mut |term| {
        if let Term::Variable { name, sort } = term {
            variables.push((name.clone(), sort.clone()));
        }
    });
    let output = (Printer::new().print_term(rule), variables);

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn semantic_cast_sort_metadata_disambiguates_manually_built_applications() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("choice", "A", Attributes::default()),
                production("choice", "B", Attributes::default()),
                rule(
                    application("#SemanticCastToA", vec![application("choice", Vec::new())]),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = resolve_semantic_casts(&definition);
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
    assert_eq!(
        body.metadata().and_then(|metadata| metadata.sort.as_ref()),
        Some(&Sort::new("A"))
    );
}

#[test]
fn adds_kitem_subsorts_for_every_non_parser_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
          syntax Data ::= "d" [symbol(d)]
          syntax #Internal ::= "internal" [symbol(internal)]
          rule a => d
        endmodule
    "#};
    let transformed = subsort_kitem(&parsed(source)).unwrap();
    let generated = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: None,
                sort,
                items,
                attributes,
                ..
            } if sort == &Sort::new("KItem") && attributes.is_empty() => match items.as_slice() {
                [ProductionItem::NonTerminal { sort: child, .. }] => {
                    Some((sort.to_string(), child.to_string()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(generated);
    });
}

#[test]
fn folds_pure_constants_only_on_rule_right_hand_sides_and_conditions() {
    let source = indoc! {r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Bool [hook(BOOL.Bool)]
          syntax Int ::= r"[\+\-]?[0-9]+" [token, prec(2)]
          syntax Bool ::= r"true|false" [token]
          syntax Int ::= "add(" Int "," Int ")" [function, hook(INT.add), symbol(add)]
          syntax Bool ::= "eq(" Int "," Int ")" [function, hook(INT.eq), symbol(eq)]
          rule add(1, 2) => add(add(1, 2), 39)
            requires eq(add(1, 1), 2)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = constant_fold(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, requires, .. } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
            )),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[cfg(feature = "mpfr-folding")]
#[test]
fn folds_mpfr_float_constants_with_their_declared_contexts() {
    let source = indoc! {r#"
        module MAIN
          syntax Float [hook(FLOAT.Float)]
          syntax Int [hook(INT.Int)]
          syntax Float ::= r"([\+\-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\+\-]?[0-9]+)?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(1)]
          syntax Float ::= "add(" Float "," Float ")" [function, hook(FLOAT.add), symbol(addFloat)]
          syntax Int ::= "exponent(" Float ")" [function, hook(FLOAT.exponent), symbol(floatExponent)]
          syntax Float ::= "floatResult" [symbol(floatResult)]
          syntax Int ::= "intResult" [symbol(intResult)]

          rule floatResult => add(0.1, 0.2)
          rule floatResult => add(3.4028235e38p24x8, 3.4028235e38p24x8)
          rule intResult => exponent(1.40129846e-45p24x8)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = constant_fold(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn folds_unicode_string_hooks_with_java_token_wrapping() {
    let string_sort = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("String"),
        attributes: attributes(&[("hook", json!("STRING.String"))]),
    };
    let concat = Sentence::Production {
        label: Some(Label::new("concat")),
        parameters: Vec::new(),
        sort: Sort::new("String"),
        items: vec![
            ProductionItem::NonTerminal {
                sort: Sort::new("String"),
                name: None,
            },
            ProductionItem::NonTerminal {
                sort: Sort::new("String"),
                name: None,
            },
        ],
        attributes: attributes(&[("function", json!("")), ("hook", json!("STRING.concat"))]),
    };
    let token = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("String"),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                string_sort,
                concat,
                rule(
                    rewrite(
                        application("result", Vec::new()),
                        application("concat", vec![token("\"λ\""), token("\"🦀\"")]),
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = constant_fold(&definition).unwrap();
    let Sentence::Rule { body, .. } = &transformed.main_module().unwrap().local_sentences[2] else {
        unreachable!()
    };
    let Term::Rewrite { right, .. } = body.unannotated() else {
        unreachable!()
    };
    assert_eq!(
        right.unannotated(),
        &Term::Token {
            token: "\"\\u03bb\\U0001f980\"".into(),
            sort: Sort::new("String"),
        }
    );
}

#[test]
fn reports_invalid_constant_operations() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: attributes(&[("hook", json!("INT.Int"))]),
                },
                Sentence::Production {
                    label: Some(Label::new("divide")),
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
                    attributes: attributes(&[("hook", json!("INT.tdiv"))]),
                },
                rule(
                    rewrite(
                        application("result", Vec::new()),
                        application(
                            "divide",
                            vec![
                                Term::Token {
                                    token: "1".into(),
                                    sort: Sort::new("Int"),
                                },
                                Term::Token {
                                    token: "0".into(),
                                    sort: Sort::new("Int"),
                                },
                            ],
                        ),
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let error = constant_fold(&definition).unwrap_err();
    assert_eq!(error.diagnostics[0].message, "Division by zero.");
}

#[test]
fn propagates_production_macro_kinds_except_to_simplification_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro-rec, symbol(m)]
          rule m(X:Exp) => X:Exp [label(expand)]
          rule m(a) => a [simplification, label(simplify)]
        endmodule
    "#};
    let transformed = propagate_macro_attributes(&parsed(source)).unwrap();
    let attributes = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { attributes, .. } => Some((
                attributes.get_str("label").map(str::to_owned),
                attributes.get("macro-rec").is_some(),
                attributes.get("simplification").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(attributes);
    });
}

#[test]
fn guards_or_patterns_with_collision_free_typed_aliases() {
    let source = indoc! {r##"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | Exp "#Or" Exp [symbol(#Or)]
          rule a #Or b
        endmodule
    "##};
    let transformed = guard_or_patterns(&parsed(source)).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn or_guards_do_not_cross_existing_alias_or_rewrite_boundaries() {
    let or = Term::Apply {
        label: Label::with_parameters("#Or", vec![Sort::new("Exp")]),
        arguments: vec![application("a", Vec::new()), application("b", Vec::new())],
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("a", "Exp", Attributes::default()),
                production("b", "Exp", Attributes::default()),
                rule(rewrite(or.clone(), or.clone()), Attributes::default()),
                Sentence::Context {
                    body: Term::As {
                        pattern: Box::new(or),
                        alias: Box::new(Term::variable("X")),
                    },
                    requires: truth(),
                    attributes: Attributes::default(),
                },
            ],
        )],
        attributes: Attributes::default(),
    };
    assert_eq!(guard_or_patterns(&definition).unwrap(), definition);
}

#[test]
fn allocates_shared_and_anonymous_fresh_configuration_constants() {
    let source = indoc! {r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "initA" [function, initializer, symbol(initA)]
                       | "initB" [function, initializer, symbol(initB)]
          rule initA => !X:Int [initializer]
          rule initB => !X:Int [initializer]
          rule initA => !_ [initializer]
          rule initB => !_ [initializer]
        endmodule
    "#};
    let definition = resolve_anon_vars(&parsed(source));
    let definition = resolve_semantic_casts(&definition);
    let (transformed, next_fresh) = resolve_fresh_config_constants(&definition).unwrap();
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let output = (bodies, next_fresh);

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn rejects_non_integer_fresh_configuration_constants() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::Rule {
                body: rewrite(
                    application("init", Vec::new()),
                    Term::Variable {
                        name: "!Fresh".into(),
                        sort: Some(Sort::new("String")),
                    },
                ),
                requires: truth(),
                ensures: truth(),
                attributes: attributes(&[("initializer", json!(""))]),
            }],
        )],
        attributes: Attributes::default(),
    };
    let error = resolve_fresh_config_constants(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].message,
        "Can't resolve fresh configuration variable not of sort Int"
    );
}

#[test]
fn generates_predicates_for_each_local_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool
          syntax Exp ::= "a" [symbol(a)]
          syntax Data ::= "d" [symbol(d)]
        endmodule
    "#};
    let transformed = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let predicates = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                sort,
                attributes,
                ..
            } if attributes.get("predicate").is_some() => Some((
                label.name.clone(),
                sort.to_string(),
                attributes.get("predicate").cloned(),
                attributes.get("total").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(predicates);
    });
}

#[test]
fn generates_generic_and_named_field_projections() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Pair ::= pair(left: Int, right: Int) [symbol(pair)]
        endmodule
    "#};
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let transformed = generate_sort_projections(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name.starts_with("project:") => Some((
                "production",
                label.name.clone(),
                attributes.get("total").is_some(),
                attributes.get("projection").is_some(),
            )),
            Sentence::Rule {
                body, attributes, ..
            } if Printer::new().print_term(body).starts_with("`project:") => Some((
                "rule",
                Printer::new().print_term(body),
                attributes.get("total").is_some(),
                attributes.get("projection").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn generated_sort_projections_are_idempotent() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Exp"),
                attributes: Attributes::default(),
            }],
        )],
        attributes: Attributes::default(),
    };
    let definition = generate_sort_predicate_syntax(&definition).unwrap();
    let once = generate_sort_projections(&definition).unwrap();
    let twice = generate_sort_projections(&once).unwrap();
    assert_eq!(once, twice);
}

#[test]
fn expands_nested_macros_child_first_in_priority_order() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "c" [symbol(c)]
                       | "m(" Exp ")" [macro, symbol(m)]
                       | "n(" Exp ")" [macro-rec, symbol(n)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
          rule m(X:Exp) => n(X:Exp) [priority(10)]
          rule n(a) => b [priority(20)]
          rule n(b) => c [owise]
          rule pair(m(a), n(b)) => pair(n(a), m(b)) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .next()
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn validates_smt_lemmas_after_expanding_aliases() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | "pow256" [alias, symbol(pow256)]
                       | "chop" "(" Int ")" [function, total, smtlib(chop), symbol(chop)]
                       | Int "mod" Int [function, total, smt-hook(mod), symbol(mod)]
          rule pow256 => 256
          rule chop(I:Int) => I mod pow256 [smt-lemma]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    assert!(
        check_definition(&resolved).unwrap().iter().all(
            |diagnostic| diagnostic.code != k_rust::diagnostic::DiagnosticCode::InvalidSmtLemma
        )
    );

    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let smt_lemma = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| sentence.attributes().get("smt-lemma").is_some())
        .unwrap();
    let Sentence::Rule { body, .. } = smt_lemma else {
        panic!("expected an SMT lemma rule");
    };
    assert!(!Printer::new().print_term(body).contains("pow256"));
}

#[test]
fn macro_matching_reuses_repeated_variables_and_freshens_unbound_rhs_variables() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "same(" Exp "," Exp ")" [macro, symbol(same)]
                       | "choose(" Exp ")" [macro, symbol(choose)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
          rule same(X:Exp, X:Exp) => X:Exp
          rule choose(X:Exp) => pair(X:Exp, Y:Exp)
          rule pair(same(a, a), choose(a)) => pair(a, a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => Some(body),
            _ => None,
        })
        .unwrap();
    let printed = Printer::new().print_term(body);
    assert!(printed.contains("pair(a(.KList),_Gen0)"), "{printed}");
}

#[test]
fn reports_a_macro_symbol_when_repeated_variable_matching_fails() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "same(" Exp "," Exp ")" [macro, symbol(same)]
          rule same(X:Exp, X:Exp) => X:Exp
          rule same(a, b) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].message,
        "Rule contains macro symbol that was not expanded"
    );
}

#[test]
fn expands_sort_constrained_variable_macros_over_tokens() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= r"[a-z]+" [token]
          syntax Exp ::= "wrap(" Foo ")" [symbol(wrap)]
          rule X:Foo => bar [macro]
          rule wrap(foo) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn rejects_macro_side_conditions_and_invalid_priorities() {
    let side_condition = indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token] | "false" [token]
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => X:Exp requires false
          rule m(a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(side_condition));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).unwrap_err();
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message == "Cannot compute macros with side conditions.")
    );

    let invalid_priority = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => X:Exp [priority(not-an-integer)]
          rule m(a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(invalid_priority));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].message,
        "Invalid value for priority attribute: not-an-integer. Must be an integer."
    );
}

#[test]
fn wraps_cell_free_rules_and_contexts_in_the_main_computation_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
                       | "f(" Exp ")" [function, symbol(f)]
                       | "g(" Exp ")" [symbol(g)]
          configuration <k> 0 </k>
          rule 1 => 2 [label(bare)]
          rule <k> 1 => 2 ... </k> [label(cell)]
          rule f(1) => 2 [label(function)]
          rule g(1) => 2 [anywhere, label(anywhere)]
          rule g(2) => 1 [simplification, label(simplification)]
          context g(HOLE) [label(context)]
        endmodule
    "#};
    let transformed = add_implicit_computation_cell(&parsed(source)).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            }
            | Sentence::Context {
                body, attributes, ..
            } => attributes
                .get_str("label")
                .map(|label| (label.to_owned(), Printer::new().print_term(body))),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn imported_syntax_rules_use_the_main_modules_computation_cell() {
    let source = indoc! {r#"
        module LANGUAGE-SYNTAX
          syntax Int ::= r"[0-9]+" [token]
          rule 1 => 2 [label(imported)]
        endmodule

        module MAIN
          imports LANGUAGE-SYNTAX
          configuration <k> 0 </k>
        endmodule
    "#};
    let transformed = add_implicit_computation_cell(&parsed(source)).unwrap();
    let body = transformed
        .modules
        .iter()
        .find(|module| module.name == "LANGUAGE-SYNTAX")
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("imported") => Some(body),
            _ => None,
        })
        .unwrap();

    assert!(matches!(
        body.unannotated(),
        Term::Apply { label, .. } if label.name == "<k>"
    ));
}

#[test]
fn wraps_a_non_function_overload_in_the_computation_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(shared)]
                       | "f" [function, symbol(shared)]
                       | "done" [symbol(done)]
          configuration <k> a </k>
          rule a => done [label(step)]
          rule f => a [label(equation)]
        endmodule
    "#};
    let transformed = add_implicit_computation_cell(&parsed(source)).unwrap();
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => attributes.get_str("label").map(|label| (label, body)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    assert!(matches!(
        bodies["step"].unannotated(),
        Term::Apply { label, .. } if label.name == "<k>"
    ));
    assert!(matches!(
        bodies["equation"].unannotated(),
        Term::Rewrite { left, .. }
            if matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "shared")
    ));
}

#[test]
fn implicit_computation_cells_require_a_declared_main_cell_only_when_needed() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                rewrite(application("a", Vec::new()), application("b", Vec::new())),
                Attributes::default(),
            )],
        )],
        attributes: Attributes::default(),
    };
    assert_eq!(
        add_implicit_computation_cell(&definition).unwrap_err(),
        "No main cell found"
    );

    let skipped = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                application("a", Vec::new()),
                attributes(&[("anywhere", json!(""))]),
            )],
        )],
        attributes: Attributes::default(),
    };
    assert_eq!(add_implicit_computation_cell(&skipped).unwrap(), skipped);
}

#[test]
fn resolves_fresh_variables_and_generates_the_counter_configuration() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int | Id
                       | "pair(" Id "," Id ")" [symbol(pair)]
          syntax Id ::= r"[a-z]+" [token]
                      | "freshId(" Int ")" [function, freshGenerator, symbol(freshId)]
          configuration <k> 0 </k>
          rule 0 => pair(!Y:Id, !X:Id) [label(fresh)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let transformed = resolve_fresh_constants(&definition, 7).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                sort,
                items,
                attributes,
                ..
            } if matches!(
                label.name.as_str(),
                "<generatedTop>" | "<generatedCounter>" | "getGeneratedCounterCell"
            ) =>
            {
                Some(format!(
                    "production {} : {sort} ({} items) format={:?}",
                    label.name,
                    items.len(),
                    attributes.get_str("format")
                ))
            }
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("fresh") => {
                Some(format!("rule {}", Printer::new().print_term(body)))
            }
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_some()
                && Printer::new()
                    .print_term(body)
                    .starts_with("initGeneratedTopCell") =>
            {
                Some(format!("initializer {}", Printer::new().print_term(body)))
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn preserves_explicit_cell_variables_while_sorting_cell_fragments() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Id ::= "freshId(" Int ")" [function, freshGenerator, symbol(freshId)]
          configuration <k> 0 </k>
          rule 0 => !X:Id
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. }
                if Printer::new()
                    .print_term(body)
                    .starts_with("getGeneratedCounterCell") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("counter projection rule should be generated");

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(body);
    });
}

#[test]
fn reports_missing_generators_for_fresh_variables() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
          configuration <k> a </k>
          rule a => !X:Exp [label(fresh)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let error = resolve_fresh_constants(&definition, 0).unwrap_err();
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "No fresh generator defined for sort Exp" })
    );
}

#[test]
fn reports_fresh_variables_without_sorts() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::Production {
                    label: Some(Label::new("<generatedTop>")),
                    parameters: Vec::new(),
                    sort: Sort::new("GeneratedTopCell"),
                    items: vec![
                        ProductionItem::Terminal("<generatedTop>".into()),
                        ProductionItem::NonTerminal {
                            sort: Sort::new("K"),
                            name: None,
                        },
                        ProductionItem::Terminal("</generatedTop>".into()),
                    ],
                    attributes: attributes(&[
                        ("cell", json!("")),
                        ("cellName", json!("generatedTop")),
                    ]),
                },
                rule(
                    rewrite(application("a", Vec::new()), Term::variable("!X")),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let error = resolve_fresh_constants(&definition, 0).unwrap_err();
    assert!(error.diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Fresh constant used without a declared sort."
    }));
}

#[test]
fn simplification_rules_require_functional_heads() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [function, symbol(f)]
                       | "w(" Exp ")" [functional, symbol(w)]
                       | "m(" Exp ")" [mlOp, symbol(m)]
                       | "c(" Exp ")" [symbol(c)]
          rule f(a) => a [simplification, label(function)]
          rule w(a) => a [simplification, label(functional)]
          rule m(a) => a [simplification, label(ml)]
        endmodule
    "#};
    assert_eq!(
        check_simplification_rules(&parsed(source)).unwrap(),
        parsed(source)
    );

    let invalid = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "c(" Exp ")" [symbol(c)]
          rule c(a) => a [simplification, label(invalid)]
        endmodule
    "#};
    let error = check_simplification_rules(&parsed(invalid)).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Simplification rules expect function/functional/mlOp symbols at the top of the left hand side term."
    );
}

#[test]
fn concretizes_nested_cells_to_declared_fixed_arities() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          configuration
            <top>
              <k> 0 </k>
              <state> 1 </state>
            </top>
          rule <k> 0 => 1 ... </k>
          rule <state> 1 => 2 </state>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none()
                && (Printer::new().print_term(body).contains("#token(\"0\"")
                    || Printer::new().print_term(body).contains("#token(\"2\"")) =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(
        !output.iter().any(|body| body.contains("#dots")),
        "{output:#?}"
    );
    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn drops_a_shallower_misnested_sibling_when_completing_parent_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <left>
                <value> 0 </value>
              </left>
              <right> 1 </right>
            </top>
          rule
            <left>
              <value> 0 => 2 </value>
              <right> 1 => 3 </right>
              ...
            </left>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none()
                && Printer::new().print_term(body).contains("#token(\"2\"") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("the labeled rule should remain");

    assert!(
        body.contains("<value>"),
        "the direct child was lost: {body}"
    );
    assert!(
        !body.contains("<right>"),
        "the shallower sibling should match Java's discarded level: {body}"
    );
}

#[test]
fn concretizes_cells_inside_generated_simplification_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <batch> 0 </batch>
            </top>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();

    for sentence in transformed
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        let Sentence::Rule { body, .. } = sentence else {
            continue;
        };
        body.visit_preorder(&mut |term| {
            if let Term::Apply { label, arguments } = term.unannotated()
                && label.name == "<batch>"
            {
                assert_eq!(arguments.len(), 1, "incomplete batch cell in {body:?}");
            }
        });
    }

    let transformed = add_semantics_module(&transformed);
    let transformed = resolve_config_var(&transformed);
    let transformed = add_cool_like_attributes(&transformed);
    let transformed = generate_sort_predicate_rules(&transformed);
    let transformed = number_sentences(&transformed);
    add_sort_injections_to_definition(&transformed).unwrap();
}

#[test]
fn does_not_wrap_matching_logic_simplifications_in_the_generated_top_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [mlOp, symbol(m)]
          configuration <k> a </k>
          rule m(a) => a [simplification]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("simplification").is_some() => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("the simplification rule should remain");

    assert!(body.starts_with("m("), "rule was wrapped in a cell: {body}");
    assert!(
        !body.contains("<generatedTop>"),
        "simplification rule gained the generated top cell: {body}"
    );
}

#[test]
fn splits_fragment_variables_on_both_sides_of_a_parent_cell_rewrite() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <k> 0 </k>
              <saved>
                <first> 1 </first>
                <second> 2 </second>
              </saved>
            </top>
          rule <k> 0 => 1 ... </k>
               <saved> _ => SAVED </saved>
        endmodule
    "#};
    let definition = resolve_anon_vars(&parsed(source));
    let definition = resolve_semantic_casts(&definition);
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();

    assert!(
        body.contains("<saved>"),
        "missing saved parent cell: {body}"
    );
    assert_eq!(
        body.matches("=>").count(),
        3,
        "the k, first, and second cells should each contain a rewrite: {body}"
    );
}

#[test]
fn lifts_one_sided_repeated_cell_rewrites_through_missing_parents() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <store>
                <items>
                  <item multiplicity="*" type="Map">
                    <id> 0 </id>
                  </item>
                </items>
              </store>
            </top>
          rule (.Bag => <item> <id> 1 </id> </item>)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .expect("the repeated-cell insertion rule should remain");

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(body);
    });
}

#[test]
fn clears_repeated_cell_contents_without_removing_the_parent() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <items>
                <item multiplicity="*" type="Map">
                  <id> 0 </id>
                </item>
              </items>
            </top>
          rule <items> _ => .Bag </items>
        endmodule
    "#};
    let definition = resolve_anon_vars(&parsed(source));
    let definition = resolve_semantic_casts(&definition);
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .expect("the repeated-cell clearing rule should remain");

    assert!(
        body.contains("`<items>`("),
        "the parent cell was removed: {body}"
    );
    assert!(
        body.contains("=>`.ItemCellMap`"),
        "the repeated contents were not cleared: {body}"
    );
}

#[test]
fn fills_absent_optional_and_repeated_cells_with_their_units() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          configuration
            <top>
              <k> 0 </k>
              <state multiplicity="?"> 1 </state>
              <thread multiplicity="*">
                <id> 0 </id>
              </thread>
            </top>
          rule <top>
            <k> 0 => 1 </k>
          </top>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none()
                && Printer::new().print_term(body).contains("#token(\"1\"") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn concretizes_parameterized_repeated_cell_initializers_as_parent_children() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <thread multiplicity="*" type="Map">
                <id> 0 </id>
                <k> $PGM:K </k>
              </thread>
            </top>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_some()
                && Printer::new().print_term(body).contains("initThreadCell")
                && Printer::new().print_term(body).contains("<top>") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("the top initializer should contain the repeated-cell initializer");

    assert!(
        body.contains("initThreadCell("),
        "the parameterized initializer was lost: {body}"
    );
}

#[test]
fn concretizes_nullary_initial_repeated_cell_initializers_as_parent_children() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <thread multiplicity="*" type="Map" initial="">
                <id> 0 </id>
              </thread>
            </top>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_some()
                && Printer::new().print_term(body).contains("initThreadCell")
                && Printer::new().print_term(body).contains("<top>") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("the top initializer should contain the repeated-cell initializer");

    assert!(
        body.contains("initThreadCell"),
        "the nullary initializer was lost: {body}"
    );
}

#[test]
fn generated_repeated_cell_initializers_conform_to_every_collection_consumer() {
    for collection in ["Map", "Set", "List"] {
        for (shape, cell_attributes, contents) in [
            ("parameterized", "", "<k> $PGM:K </k>"),
            ("nullary", " initial=\"\"", "<id> 0 </id>"),
        ] {
            let source = format!(
                r#"
                module MAIN
                  syntax Int ::= r"[0-9]+" [token]
                  configuration
                    <top>
                      <entry multiplicity="*" type="{collection}"{cell_attributes}>
                        {contents}
                      </entry>
                    </top>
                endmodule
                "#
            );
            let definition = resolve_semantic_casts(&parsed(&source));
            let definition = add_implicit_computation_cell(&definition).unwrap();
            let definition = resolve_fresh_constants(&definition, 0).unwrap();
            let transformed = concretize_cells(&definition).unwrap_or_else(|error| {
                panic!("{collection}/{shape} generated an incompatible construct: {error}")
            });
            let top_initializer = transformed
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .find_map(|sentence| match sentence {
                    Sentence::Rule {
                        body, attributes, ..
                    } if attributes.get("initializer").is_some()
                        && Printer::new().print_term(body).contains("initEntryCell")
                        && Printer::new().print_term(body).contains("<top>") =>
                    {
                        Some(Printer::new().print_term(body))
                    }
                    _ => None,
                })
                .unwrap_or_else(|| {
                    panic!("{collection}/{shape} lost its generated repeated-cell initializer")
                });

            assert!(top_initializer.contains("initEntryCell"));
        }
    }
}

#[test]
fn splits_cell_fragment_variables_and_rebuilds_external_occurrences() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "isTopCellFragment" "(" TopCellFragment ")"
            [function, symbol(isTopCellFragment)]
          syntax Bool ::= "ok" "(" TopCellFragment ")" [function, symbol(ok)]
          configuration
            <top>
              <k> 0 </k>
              <state> 1 </state>
              <env> 2 </env>
            </top>
          rule <top>
            <k> 0 => 1 ... </k>
            CELLS:TopCellFragment
          </top>
          requires isTopCellFragment(CELLS)
          ensures ok(CELLS)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
                ..
            } if attributes.get("initializer").is_none() => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
                Printer::new().print_term(ensures),
            )),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn finalizes_language_parsing_and_sort_predicate_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
        endmodule
    "#};
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let definition = add_semantics_module(&definition);
    let definition = number_sentences(&generate_sort_predicate_rules(&definition));
    let language = definition
        .modules
        .iter()
        .find(|module| module.name == "LANGUAGE-PARSING")
        .unwrap();
    assert_eq!(
        language
            .imports
            .iter()
            .map(|import| import.name.as_str())
            .collect::<Vec<_>>(),
        ["MAIN"]
    );
    let predicates = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if Printer::new().print_term(body).starts_with("isExp(") => Some((
                Printer::new().print_term(body),
                attributes.get("owise").is_some(),
                attributes.get_str("UNIQUE_ID").map(str::to_owned),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(predicates);
    });
}

#[test]
fn marks_variable_headed_main_cell_sequences_as_cool_like() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> 0 </k>
          rule <k> REST:K ~> 0 => REST ... </k>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let definition = concretize_cells(&definition).unwrap();
    let definition = add_cool_like_attributes(&definition);
    let rendered = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => Some((Printer::new().print_term(body), attributes.entries())),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(
                |sentence| matches!(sentence, Sentence::Rule { attributes, .. }
            if attributes.get("initializer").is_none()
                && attributes.get("cool-like").is_some())
            ),
        "{rendered:#?}"
    );
}

#[test]
fn generates_left_to_right_seqstrict_contexts_and_imports_bool() {
    let source = indoc! {r#"
        module BOOL
        endmodule

        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | Exp "+" Exp [seqstrict, symbol(_+_)]
        endmodule
    "#};
    let transformed = resolve_strict(&parsed(source)).unwrap();
    let main = transformed.main_module().unwrap();
    assert_eq!(
        main.imports
            .iter()
            .filter(|import| import.name == "BOOL" && !import.public)
            .count(),
        1
    );
    let contexts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
                attributes.get_str("label").map(str::to_owned),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(contexts);
    });
}

#[test]
fn expands_context_alias_groups_context_rewrites_and_hybrid_rules() {
    let alias = Sentence::ContextAlias {
        body: application("wrapper", vec![Term::variable("HERE")]),
        requires: application("allowed", vec![Term::variable("K0")]),
        attributes: attributes(&[
            ("label", json!("custom")),
            ("context", json!("resume")),
            ("result", json!("Foo")),
        ]),
    };
    let strict = Sentence::Production {
        label: Some(Label::new("step")),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![
            ProductionItem::NonTerminal {
                sort: Sort::new("Exp"),
                name: None,
            },
            ProductionItem::NonTerminal {
                sort: Sort::new("Exp"),
                name: None,
            },
        ],
        attributes: attributes(&[("seqstrict", json!("custom;1,2")), ("hybrid", json!("Foo"))]),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module("MAIN", vec![alias, strict]),
        ],
        attributes: Attributes::default(),
    };

    let transformed = resolve_strict(&definition).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        !main
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::ContextAlias { .. }))
    );
    let contexts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Context { body, requires, .. } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(contexts.len(), 2);
    assert!(
        contexts
            .iter()
            .all(|(body, _)| body.contains("#SemanticCastToExp(HOLE)=>resume")),
        "{contexts:#?}"
    );
    assert!(contexts[1].1.contains("isFoo(K0)"), "{contexts:#?}");
    assert!(main.local_sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Rule { body, requires, .. }
            if Printer::new().print_term(body).starts_with("isFoo(step(")
                && Printer::new().print_term(requires).contains("isFoo(K0)")
                && Printer::new().print_term(requires).contains("isFoo(K1)"))
    }));
}

#[test]
fn rejects_strictness_aliases_that_do_not_exist() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module(
                "MAIN",
                vec![Sentence::Production {
                    label: Some(Label::new("step")),
                    parameters: Vec::new(),
                    sort: Sort::new("Exp"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Exp"),
                        name: None,
                    }],
                    attributes: attributes(&[("strict", json!("missing"))]),
                }],
            ),
        ],
        attributes: Attributes::default(),
    };

    let error = resolve_strict(&definition).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Found rule label \"missing\" in strictness attribute which did not refer to any sentence."
    );
}

#[test]
fn gives_anonymous_variables_collision_free_sentence_local_names() {
    let first = Sentence::Rule {
        body: application(
            "pair",
            vec![
                Term::variable("_Gen0"),
                Term::Variable {
                    name: "_".into(),
                    sort: Some(Sort::new("Exp")),
                },
                Term::variable("?_"),
            ],
        ),
        requires: application("needs", vec![Term::variable("!_")]),
        ensures: application("keeps", vec![Term::variable("@_")]),
        attributes: Attributes::default(),
    };
    let second = rule(
        application("other", vec![Term::variable("_")]),
        Attributes::default(),
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module("MAIN", vec![first, second])],
        attributes: Attributes::default(),
    };

    let transformed = resolve_anon_vars(&definition);
    let rendered = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
                Printer::new().print_term(ensures),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered[0].0.contains("_Gen0,_Gen1,?_Gen2"),
        "{rendered:#?}"
    );
    assert!(rendered[0].1.contains("!_Gen3"), "{rendered:#?}");
    assert!(rendered[0].2.contains("@_Gen4"), "{rendered:#?}");
    assert!(rendered[1].0.contains("_Gen0"), "{rendered:#?}");
}

#[test]
fn lowers_contexts_to_freezer_heat_and_cool_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [symbol(f)]
          context f(HOLE)
        endmodule
    "#};
    let transformed = resolve_contexts(&resolve_anon_vars(&parsed(source))).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        !main
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Context { .. }))
    );
    let generated = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } if label.name.starts_with("#freezer") => Some(("freezer", label.name.clone(), None)),
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("heat").is_some() || attributes.get("cool").is_some() => Some((
                if attributes.get("heat").is_some() {
                    "heat"
                } else {
                    "cool"
                },
                Printer::new().print_term(body),
                attributes.get_str("label").map(str::to_owned),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(generated);
    });
}

#[test]
fn inserts_context_rewrites_inside_the_main_cell() {
    let context = Sentence::Context {
        body: incomplete_cell(
            "<k>",
            application("f", vec![Term::variable("HOLE"), Term::variable("X")]),
        ),
        requires: truth(),
        attributes: attributes(&[("label", json!("evaluate"))]),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::Production {
                    label: Some(Label::new("<k>")),
                    parameters: Vec::new(),
                    sort: Sort::new("KCell"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    }],
                    attributes: attributes(&[("maincell", json!(""))]),
                },
                context,
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_contexts(&definition).unwrap();
    let rules = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("heat").is_some() || attributes.get("cool").is_some() => Some((
                Printer::new().print_term(body),
                attributes.get_str("label").unwrap().to_owned(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 2);
    assert!(
        rules
            .iter()
            .all(|(body, _)| body.starts_with("`<k>`(#noDots(.KList),")),
        "{rules:#?}"
    );
    assert!(rules.iter().any(|(_, label)| label == "evaluate-heat"));
    assert!(rules.iter().any(|(_, label)| label == "evaluate-cool"));
}

#[test]
fn rejects_invalid_context_shapes() {
    let cases = [
        (
            application("f", vec![Term::variable("X")]),
            "Contexts must have at least one HOLE.",
        ),
        (
            application(
                "f",
                vec![
                    rewrite(Term::variable("HOLE"), Term::variable("X")),
                    rewrite(Term::variable("HOLE"), Term::variable("Y")),
                ],
            ),
            "Cannot compile a context with multiple rewrites.",
        ),
        (
            application(
                "f",
                vec![
                    Term::variable("HOLE"),
                    rewrite(Term::variable("X"), Term::variable("Y")),
                ],
            ),
            "Only the HOLE can be rewritten in a context definition",
        ),
    ];
    for (body, expected) in cases {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module(
                "MAIN",
                vec![Sentence::Context {
                    body,
                    requires: truth(),
                    attributes: Attributes::default(),
                }],
            )],
            attributes: Attributes::default(),
        };
        let error = resolve_contexts(&definition).unwrap_err();
        assert_eq!(error.diagnostics[0].message, expected);
    }
}

#[test]
fn reuses_lhs_subterms_on_rule_right_hand_sides() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool [hook(BOOL.Bool)]
          syntax Bool ::= r"true|false" [token]
          syntax Exp ::= "wrap(" Bool ")" [symbol(wrap)]
          rule wrap(false) => wrap(false)
          rule wrap(true) => wrap(true) [simplification]
        endmodule
    "#};
    let transformed = minimize_term_construction(&parsed(source)).unwrap();
    let rules = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
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
fn minimizes_imported_aliases_with_symbols_generated_in_the_main_module() {
    let generated_top = Sentence::Production {
        label: Some(Label::new("<generatedTop>")),
        parameters: Vec::new(),
        sort: Sort::new("GeneratedTopCell"),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("Cell"),
            name: None,
        }],
        attributes: Attributes::default(),
    };
    let top = application("<generatedTop>", vec![application("cell", Vec::new())]);
    let aliased = Term::As {
        pattern: Box::new(top.clone()),
        alias: Box::new(Term::Variable {
            name: "#Configuration".into(),
            sort: Some(Sort::new("GeneratedTopCell")),
        }),
    };
    let mut main = module("MAIN", vec![generated_top]);
    main.imports.push(FlatImport {
        name: "LIB".into(),
        public: true,
    });
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module(
                "LIB",
                vec![
                    production("cell", "Cell", Attributes::default()),
                    rule(rewrite(aliased, top), Attributes::default()),
                ],
            ),
            main,
        ],
        attributes: Attributes::default(),
    };

    let transformed = minimize_term_construction(&definition)
        .expect("main-module generated symbols should sort imported aliases");
    let rendered = transformed
        .modules
        .iter()
        .find(|module| module.name == "LIB")
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();
    assert!(rendered.contains("_Gen"), "{rendered}");
}

#[test]
fn removes_associative_units_from_rules_only() {
    let collection_attributes = attributes(&[("assoc", json!("")), ("unit", json!(".Items"))]);
    let unit = || application(".Items", vec![]);
    let concat = |left, right| application("_Items_", vec![left, right]);
    let nested = concat(
        concat(application("a", vec![]), unit()),
        concat(unit(), application("b", vec![])),
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("_Items_", "Items", collection_attributes),
                production(".Items", "Items", Attributes::default()),
                production("a", "Items", Attributes::default()),
                production("b", "Items", Attributes::default()),
                rule(rewrite(nested.clone(), nested), Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = remove_unit(&definition).unwrap();
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
    assert_eq!(
        Printer::new().print_term(body),
        "`_Items_`(a(.KList),b(.KList))=>`_Items_`(a(.KList),b(.KList))"
    );
}

#[test]
fn preserves_optional_cell_units() {
    let attributes = attributes(&[
        ("assoc", json!("")),
        ("unit", json!("noCell")),
        ("cell", json!("")),
        ("multiplicity", json!("?")),
    ]);
    let body = application("cells", vec![application("noCell", vec![])]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("cells", "Cell", attributes),
                rule(body.clone(), Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = remove_unit(&definition).unwrap();
    let preserved = transformed.main_module().unwrap().local_sentences[1].clone();
    assert!(matches!(preserved, Sentence::Rule { body: actual, .. } if actual == body));
}
