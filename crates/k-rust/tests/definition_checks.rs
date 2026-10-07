use std::collections::{BTreeMap, BTreeSet};

use std::sync::Arc;

use k_rust::definition::{
    Associativity, Attributes, CheckMode, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE,
    PartialOrder, ProductionCatalog, ProductionItem, ResolvedModule, SOURCE_ATTRIBUTE, Sentence,
    SortCatalog, StructuralCheckBackend, StructuralCheckOptions, check_anonymous_variables,
    check_associativity, check_attribute_semantics, check_attributes, check_configuration_cells,
    check_definition, check_duplicate_klabels, check_duplicate_labels,
    check_function_rule_attributes, check_functions, check_holes, check_k_terms, check_klabels,
    check_module, check_module_with_options, check_rewrites, check_rhs_variables,
    check_sort_top_uniqueness, check_streams, check_syntax_groups, check_tokens,
    compute_priorities,
};
use k_rust::diagnostic::{Diagnostic, DiagnosticCode, Severity};
use k_rust::kast::{Label, Sort, Term};
use k_rust::kast::{ProductionIdentity, TermMetadata};
use serde_json::{Value, json};

fn attrs(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn token(value: &str) -> Term {
    Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    }
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn as_pattern(pattern: Term, alias: Term) -> Term {
    Term::As {
        pattern: Box::new(pattern),
        alias: Box::new(alias),
    }
}

fn located() -> Attributes {
    attrs(&[
        (SOURCE_ATTRIBUTE, json!("checks.k")),
        (LOCATION_ATTRIBUTE, json!([1, 1, 1, 20])),
    ])
}

fn rule(attributes: Attributes) -> Sentence {
    Sentence::Rule {
        body: truth(),
        requires: truth(),
        ensures: truth(),
        attributes,
    }
}

fn production(
    label: Option<&str>,
    sort: &str,
    arguments: &[&str],
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: label.map(Label::new),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: arguments
            .iter()
            .map(|argument| ProductionItem::NonTerminal {
                sort: Sort::new(*argument),
                name: None,
            })
            .collect(),
        attributes,
    }
}

fn i107_syntax_sort(sort: &str) -> Arc<Sentence> {
    Arc::new(Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new(sort),
        attributes: Attributes::default(),
    })
}

fn resolved_definition(
    main_module: &str,
    modules: Vec<FlatModule>,
) -> k_rust::definition::ResolvedDefinition {
    k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: main_module.into(),
        modules,
        attributes: Attributes::default(),
    })
    .unwrap()
}

#[test]
fn claims_are_rejected_in_definitions_and_allowed_in_spec_modules() {
    let claim = Sentence::Claim {
        body: rewrite(token("0"), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: located(),
    };
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Int"),
                i107_syntax_sort("Bool"),
                claim.clone().into(),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition_with_options(
        &definition,
        StructuralCheckOptions::default(),
    )
    .unwrap();
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::ClaimInDefinition
            && diagnostic.message == "Claims are not allowed in the definition."
    }));

    let proof = resolved_definition(
        "SPEC",
        vec![
            FlatModule {
                name: "DEF".into(),
                imports: Vec::new(),
                local_sentences: vec![i107_syntax_sort("Int"), i107_syntax_sort("Bool")],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "SPEC".into(),
                imports: vec![FlatImport {
                    name: "DEF".into(),
                    public: true,
                }],
                local_sentences: vec![Arc::new(claim)],
                attributes: Attributes::default(),
            },
        ],
    );
    let diagnostics = k_rust::definition::check_definition_with_options(
        &proof,
        StructuralCheckOptions {
            mode: CheckMode::Proof {
                definition_module: "DEF".into(),
            },
            ..StructuralCheckOptions::default()
        },
    )
    .unwrap();
    assert!(
        !diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == DiagnosticCode::ClaimInDefinition })
    );
}

#[test]
fn proof_modules_admit_only_claims_simplifications_and_existing_sort_tokens() {
    let ordinary_rule = Sentence::Rule {
        body: rewrite(token("0"), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: located(),
    };
    let simplification_rule = Sentence::Rule {
        body: rewrite(token("0"), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("simplification", json!(""))]),
    };
    let existing_token = Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new("Int"),
        items: vec![ProductionItem::RegexTerminal {
            regex: "[0-9]+".into(),
            precede_regex: None,
            follow_regex: None,
        }],
        attributes: attrs(&[("token", json!(""))]),
    };
    let proof = resolved_definition(
        "SPEC",
        vec![
            FlatModule {
                name: "DEF".into(),
                imports: Vec::new(),
                local_sentences: vec![i107_syntax_sort("Int"), i107_syntax_sort("Bool")],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "SPEC".into(),
                imports: vec![FlatImport {
                    name: "DEF".into(),
                    public: true,
                }],
                local_sentences: vec![
                    i107_syntax_sort("Fresh"),
                    Arc::new(production(
                        Some("fresh"),
                        "Fresh",
                        &[],
                        Attributes::default(),
                    )),
                    Arc::new(existing_token),
                    Arc::new(ordinary_rule),
                    Arc::new(simplification_rule),
                ],
                attributes: Attributes::default(),
            },
        ],
    );
    let diagnostics = k_rust::definition::check_definition_with_options(
        &proof,
        StructuralCheckOptions {
            mode: CheckMode::Proof {
                definition_module: "DEF".into(),
            },
            ..StructuralCheckOptions::default()
        },
    )
    .unwrap();

    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::ProofModuleSyntax)
            .count(),
        2
    );
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::ProofModuleRule)
            .count(),
        1
    );
}

#[test]
fn is_sort_predicate_conflicts_match_kompile() {
    let predicate = |name: &str, arguments: &[&str]| Sentence::Production {
        label: Some(Label::new(name)),
        parameters: Vec::new(),
        sort: Sort::new("Bool"),
        items: std::iter::once(ProductionItem::Terminal(name.into()))
            .chain(std::iter::once(ProductionItem::Terminal("(".into())))
            .chain(arguments.iter().map(|sort| ProductionItem::NonTerminal {
                sort: Sort::new(*sort),
                name: None,
            }))
            .chain(std::iter::once(ProductionItem::Terminal(")".into())))
            .collect(),
        attributes: attrs(&[("function", json!(""))]),
    };
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Bool"),
                i107_syntax_sort("KItem"),
                i107_syntax_sort("Foo"),
                i107_syntax_sort("NonAddr"),
                Arc::new(predicate("isNonAddr", &["KItem"])),
                Arc::new(predicate("isNonAddr", &["Foo"])),
                Arc::new(predicate("isNonAddr", &["KItem", "KItem"])),
                Arc::new(predicate("isFoo", &["Foo"])),
                Arc::new(predicate("isnonaddr", &["KItem"])),
                Arc::new(predicate("isNotASort", &["KItem"])),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition(&definition).unwrap();
    let conflicts = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::IsSortPredicateConflict)
        .collect::<Vec<_>>();
    assert_eq!(conflicts.len(), 4);
    assert!(conflicts.iter().all(|diagnostic| {
        diagnostic
            .message
            .starts_with("Syntax declaration conflicts with automatically generated is")
    }));
}

/// A declared `isS` conflicts only with a predicate compilation generates, which it does for the
/// sorts whose role has a sort predicate. A numeral, a `#` sort and `KList` have no K terms and
/// no generated predicate, so declaring theirs conflicts with nothing; a defined sort is the
/// control.
#[test]
fn is_sort_predicate_conflicts_only_with_generated_predicates() {
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Bool"),
                i107_syntax_sort("K"),
                i107_syntax_sort("KList"),
                i107_syntax_sort("8"),
                i107_syntax_sort("#Foo"),
                i107_syntax_sort("Foo"),
                Arc::new(i107_is_sort_predicate("is8", "K")),
                Arc::new(i107_is_sort_predicate("is#Foo", "K")),
                Arc::new(i107_is_sort_predicate("isKList", "K")),
                Arc::new(i107_is_sort_predicate("isFoo", "K")),
            ],
            attributes: Attributes::default(),
        }],
    );
    let conflicts = i107_is_sort_conflicts(&definition, StructuralCheckOptions::default());
    assert_eq!(
        conflicts
            .iter()
            .map(|diagnostic| diagnostic.message.as_str())
            .collect::<Vec<_>>(),
        ["Syntax declaration conflicts with automatically generated isFoo predicate."]
    );
}

fn i107_is_sort_predicate(name: &str, argument: &str) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(name)),
        parameters: Vec::new(),
        sort: Sort::new("Bool"),
        items: vec![
            ProductionItem::Terminal(name.into()),
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new(argument),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes: attrs(&[("function", json!(""))]),
    }
}

/// A module that declares `Range` and either carries a rule bubble or is syntax-only.
fn i107_range_module(name: &str, with_rule: bool) -> FlatModule {
    let mut local_sentences = vec![i107_syntax_sort("Range")];
    if with_rule {
        local_sentences.push(rule(located()).into());
    }
    FlatModule {
        name: name.into(),
        imports: Vec::new(),
        local_sentences,
        attributes: Attributes::default(),
    }
}

/// The main module of the MIR shape: a user `isRange(Value)` predicate without a `Range` sort.
fn i107_is_range_main(name: &str) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: Vec::new(),
        local_sentences: vec![
            i107_syntax_sort("Bool"),
            i107_syntax_sort("Value"),
            Arc::new(i107_is_sort_predicate("isRange", "Value")),
        ],
        attributes: Attributes::default(),
    }
}

fn i107_is_sort_conflicts(
    definition: &k_rust::definition::ResolvedDefinition,
    options: StructuralCheckOptions,
) -> Vec<Diagnostic> {
    k_rust::definition::check_definition_with_options(definition, options)
        .unwrap()
        .into_iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::IsSortPredicateConflict)
        .collect()
}

#[test]
fn is_sort_predicate_ignores_sorts_outside_the_parsed_definition() {
    // reference: DefinitionParsing.parseDefinitionAndResolveBubbles retains the main closure and
    // only entry modules whose visible sentences hold no bubble; Kompile.checkIsSortPredicates
    // never sees a rule-bearing module that nothing imports (isSortPredicateBubbleModule.k and
    // isSortPredicateOutsideClosure.k both exit 0 under k/result/bin/kompile).
    let definition = resolved_definition(
        "MAIN",
        vec![
            i107_range_module("RANGE-RULES", true),
            i107_is_range_main("MAIN"),
        ],
    );
    let conflicts = i107_is_sort_conflicts(&definition, StructuralCheckOptions::default());
    assert_eq!(conflicts, Vec::new());
}

#[test]
fn is_sort_predicate_sees_bubble_free_entry_modules() {
    // reference: a syntax-only module that nothing imports is an entry module of the parsed
    // definition, so its Range generates isRange (isSortPredicateEntryModule.k exits 113).
    let definition = resolved_definition(
        "MAIN",
        vec![
            i107_range_module("RANGE-SYNTAX", false),
            i107_is_range_main("MAIN"),
        ],
    );
    let conflicts = i107_is_sort_conflicts(&definition, StructuralCheckOptions::default());
    assert_eq!(conflicts.len(), 1);
    assert_eq!(
        conflicts[0].message,
        "Syntax declaration conflicts with automatically generated isRange predicate."
    );
}

#[test]
fn is_sort_predicate_sees_frontend_utility_modules() {
    // reference: parseDefinitionAndResolveBubbles always retains K-REFLECTION, STDIN-STREAM,
    // STDOUT-STREAM, and MAP with their import closures, bubbles or not.
    for utility in ["K-REFLECTION", "STDIN-STREAM", "STDOUT-STREAM", "MAP"] {
        let definition = resolved_definition(
            "MAIN",
            vec![i107_range_module(utility, true), i107_is_range_main("MAIN")],
        );
        let conflicts = i107_is_sort_conflicts(&definition, StructuralCheckOptions::default());
        assert_eq!(conflicts.len(), 1, "{utility}");
    }
}

#[test]
fn is_sort_predicate_sees_the_definition_module_closure_in_proof_mode() {
    // reference: ProofDefinitionBuilder.build passes the definition module's closure together
    // with the specification module's closure to Kompile.structuralChecks.
    let definition = resolved_definition(
        "SPEC",
        vec![i107_range_module("DEF", true), i107_is_range_main("SPEC")],
    );
    let proof = StructuralCheckOptions {
        mode: CheckMode::Proof {
            definition_module: "DEF".into(),
        },
        ..StructuralCheckOptions::default()
    };
    assert_eq!(i107_is_sort_conflicts(&definition, proof).len(), 1);
    assert_eq!(
        i107_is_sort_conflicts(&definition, StructuralCheckOptions::default()),
        Vec::new()
    );
}

#[test]
fn unused_symbols_follow_check_klabels_exemptions() {
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Bool"),
                i107_syntax_sort("Int"),
                i107_syntax_sort("Foo"),
                i107_syntax_sort("Bar"),
                Arc::new(production(Some("foo"), "Foo", &["Int"], located())),
                Arc::new(production(
                    Some("bar"),
                    "Bar",
                    &["Int"],
                    attrs(&[
                        ("unused", json!("")),
                        (SOURCE_ATTRIBUTE, json!("checks.k")),
                        (LOCATION_ATTRIBUTE, json!([2, 1, 2, 20])),
                    ]),
                )),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition_with_options(
        &definition,
        StructuralCheckOptions {
            builtin_source_prefixes: vec!["krust-builtin://".into()],
            ..StructuralCheckOptions::default()
        },
    )
    .unwrap();
    let unused = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::UnusedSymbol)
        .collect::<Vec<_>>();
    assert_eq!(unused.len(), 1);
    assert_eq!(
        unused[0].message,
        "Symbol 'foo' defined but not used. Add the 'unused' attribute if this is intentional."
    );
}

#[test]
fn unused_symbols_count_uses_in_claims() {
    // A claim is a sentence of the specification: a symbol it applies is used, because deleting
    // the production would break the claim. The unused control production keeps the check
    // observable, so the test cannot pass by the check not running.
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Bool"),
                i107_syntax_sort("Int"),
                i107_syntax_sort("Foo"),
                i107_syntax_sort("Bar"),
                Arc::new(production(Some("foo"), "Foo", &["Int"], located())),
                Arc::new(production(
                    Some("bar"),
                    "Bar",
                    &["Int"],
                    attrs(&[
                        (SOURCE_ATTRIBUTE, json!("checks.k")),
                        (LOCATION_ATTRIBUTE, json!([2, 1, 2, 20])),
                    ]),
                )),
                Arc::new(Sentence::Claim {
                    body: rewrite(Term::apply("foo", vec![token("0")]), token("0")),
                    requires: truth(),
                    ensures: truth(),
                    attributes: Attributes::default(),
                }),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition_with_options(
        &definition,
        StructuralCheckOptions {
            builtin_source_prefixes: vec!["krust-builtin://".into()],
            ..StructuralCheckOptions::default()
        },
    )
    .unwrap();
    let unused = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::UnusedSymbol)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        unused,
        ["Symbol 'bar' defined but not used. Add the 'unused' attribute if this is intentional."]
    );
}

#[test]
fn duplicate_overload_sets_warn_once_per_disconnected_component() {
    let overload = |label: &str, result: &str, arity: usize, line: usize| {
        production(
            Some(label),
            result,
            &vec![result; arity],
            attrs(&[
                ("overload", json!("foo")),
                ("unused", json!("")),
                (SOURCE_ATTRIBUTE, json!("overloads.k")),
                (LOCATION_ATTRIBUTE, json!([line, 1, line, 20])),
            ]),
        )
    };
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Foo1"),
                i107_syntax_sort("Foo2"),
                Arc::new(production(None, "Foo1", &["Foo2"], Attributes::default())),
                Arc::new(overload("foo1", "Foo1", 1, 4)),
                Arc::new(overload("foo2", "Foo2", 1, 5)),
                Arc::new(overload("foo11", "Foo1", 2, 6)),
                Arc::new(overload("foo22", "Foo2", 2, 7)),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition(&definition).unwrap();
    let duplicates = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::DuplicateOverload)
        .collect::<Vec<_>>();
    assert_eq!(duplicates.len(), 2);
    assert!(duplicates.iter().all(|diagnostic| {
        diagnostic.message
            == "Overload `foo` is not unique. Consider renaming one of the overload sets with this key."
    }));
}

#[test]
fn deprecated_productions_are_reported_per_use() {
    let deprecated = production(Some("foo"), "Foo", &[], attrs(&[("deprecated", json!(""))]));
    let wrapper = production(Some("baz"), "Foo", &["Foo"], Attributes::default());
    let catalog = ProductionCatalog::from_visible([&deprecated, &wrapper]);
    let deprecated_id = catalog
        .productions()
        .find_map(|(id, sentence)| {
            matches!(sentence, Sentence::Production { label: Some(label), .. } if label.name == "foo")
                .then_some(id)
        })
        .unwrap();
    let use_deprecated = || {
        Term::apply("foo", Vec::new()).with_metadata(TermMetadata {
            production: Some(
                ProductionIdentity::from_hex(&format!("{:032x}", deprecated_id.0)).unwrap(),
            ),
            ..TermMetadata::default()
        })
    };
    let sentence = Sentence::Rule {
        body: rewrite(
            Term::apply("baz", vec![use_deprecated()]),
            Term::apply("baz", vec![use_deprecated()]),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: located(),
    };
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Bool"),
                i107_syntax_sort("Foo"),
                Arc::new(deprecated),
                Arc::new(wrapper),
                Arc::new(sentence),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition(&definition).unwrap();
    let deprecated = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::DeprecatedProduction)
        .collect::<Vec<_>>();
    assert_eq!(deprecated.len(), 2);
    assert!(deprecated.iter().all(|diagnostic| {
        diagnostic.message
            == "Use of deprecated production found; this syntax may be removed in the future."
    }));
}

#[test]
fn klabel_overloads_use_the_migration_warning_variant() {
    let definition = resolved_definition(
        "MAIN",
        vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                i107_syntax_sort("Bool"),
                i107_syntax_sort("Foo"),
                i107_syntax_sort("Bar"),
                Arc::new(production(None, "Foo", &["Bar"], Attributes::default())),
                Arc::new(production(
                    Some("fooFoo"),
                    "Foo",
                    &["Foo"],
                    attrs(&[("klabel", json!("foo"))]),
                )),
                Arc::new(production(
                    Some("fooBar"),
                    "Bar",
                    &["Bar"],
                    attrs(&[("klabel", json!("foo"))]),
                )),
            ],
            attributes: Attributes::default(),
        }],
    );
    let diagnostics = k_rust::definition::check_definition(&definition).unwrap();
    let migrations = diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.message
                == "Attribute `klabel(foo) is deprecated, but marks an overload. Add `overload(foo)`."
        })
        .count();
    assert_eq!(migrations, 2, "{diagnostics:#?}");
    assert!(!diagnostics.iter().any(|diagnostic| {
        diagnostic.message
            == "Attribute `klabel(_)` is deprecated. Either remove `klabel(foo)`, or replace it by `symbol(foo)`."
    }));
}

#[test]
fn anonymous_variables_in_symbolic_requires_are_legal() {
    let anonymous = Term::variable("_");
    let sentence = Sentence::Rule {
        body: rewrite(token("0"), token("0")),
        requires: Term::apply(
            "#Exists",
            vec![anonymous.clone(), Term::apply("predicate", vec![anonymous])],
        ),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let diagnostics = check_rhs_variables(
        &[&sentence],
        StructuralCheckOptions {
            symbolic: true,
            backend: StructuralCheckBackend::Rust,
            ..StructuralCheckOptions::default()
        },
    );
    assert!(
        !diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == DiagnosticCode::UnboundVariable })
    );
}

#[test]
fn duplicate_labels_ignore_context_aliases_and_preserve_location() {
    let located = attrs(&[
        ("label", json!("same")),
        (SOURCE_ATTRIBUTE, json!("definition.k")),
        (LOCATION_ATTRIBUTE, json!([3, 4, 3, 12])),
    ]);
    let first = rule(attrs(&[("label", json!("same"))]));
    let second = rule(located);
    let alias = Sentence::ContextAlias {
        body: truth(),
        requires: truth(),
        attributes: attrs(&[("label", json!("same"))]),
    };
    let diagnostics = check_duplicate_labels(&[&first, &second, &alias]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::DuplicateSentenceLabel);
    assert_eq!(diagnostics[0].severity, Severity::Error);
    assert_eq!(diagnostics[0].source.as_deref(), Some("definition.k"));
    assert_eq!(diagnostics[0].location.unwrap().start_column, 4);
}

#[test]
fn syntax_groups_warn_when_tags_have_different_priorities() {
    let priority = Sentence::SyntaxPriority {
        priorities: vec![vec!["high".into()], vec!["low".into()]],
        attributes: Attributes::default(),
    };
    let group = Sentence::SyntaxAssociativity {
        associativity: Associativity::Left,
        tags: vec!["low".into(), "unrelated".into(), "high".into()],
        attributes: Attributes::default(),
    };
    let priorities = compute_priorities([&priority]).unwrap();
    let diagnostics = check_syntax_groups(&[&group], &priorities);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].severity, Severity::Warning);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidAssociativity);
    assert_eq!(
        diagnostics[0].message,
        "Symbols high and low are in the same associativity group, but have different priorities."
    );
}

#[test]
fn associativity_attributes_are_rejected_where_the_result_sort_cannot_nest() {
    let invalid = production(
        Some("op"),
        "Expr",
        &["Left", "Right"],
        attrs(&[
            ("left", json!("")),
            ("right", json!("")),
            ("non-assoc", json!("")),
        ]),
    );
    let unary = production(
        Some("unary"),
        "Expr",
        &["Other"],
        attrs(&[("left", json!(""))]),
    );
    let subsorts = PartialOrder::new([(Sort::new("Unused"), Sort::new("Top"))]).unwrap();
    let diagnostics = check_associativity(&[&invalid, &unary], &subsorts);

    assert_eq!(diagnostics.len(), 3);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == DiagnosticCode::InvalidAssociativity)
    );
    assert!(diagnostics[0].message.contains("attribute not permitted"));
    assert!(diagnostics[0].message.contains("Hint:"));
}

#[test]
fn detects_multiple_top_sorts_but_exempts_cell() {
    let sort_a = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("A"),
        attributes: Attributes::default(),
    };
    let cell = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Cell"),
        attributes: Attributes::default(),
    };
    let subsorts = PartialOrder::new([
        (Sort::new("A"), Sort::new("KList")),
        (Sort::new("A"), Sort::new("Bag")),
        (Sort::new("Cell"), Sort::new("KList")),
        (Sort::new("Cell"), Sort::new("Bag")),
    ])
    .unwrap();
    let diagnostics = check_sort_top_uniqueness(&[&sort_a, &cell], &subsorts);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::MultipleTopSorts);
    assert_eq!(
        diagnostics[0].message,
        "Multiple top sorts found for A: KList and Bag."
    );
}

#[test]
fn token_sort_productions_reject_only_user_sort_constructors() {
    let illegal = production(Some("ordinary"), "Int", &[], Attributes::default());
    let function = production(
        Some("function"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let macro_production = production(Some("macro"), "Int", &[], Attributes::default());
    let internal = production(Some("internal"), "#Internal", &[], Attributes::default());

    // Create sort declarations with token attribute
    let int_decl = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Int"),
        attributes: attrs(&[("token", json!(""))]),
    };
    let internal_decl = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("#Internal"),
        attributes: attrs(&[("token", json!(""))]),
    };

    let sort_catalog =
        k_rust::definition::SortCatalog::new(vec![&int_decl, &internal_decl], vec![]);

    let macro_labels = [k_rust::definition::LabelHead::new("macro")]
        .into_iter()
        .collect();
    let diagnostics = check_tokens(
        &[&illegal, &function, &macro_production, &internal],
        &sort_catalog,
        &macro_labels,
    );

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidTokenProduction);
}

#[test]
fn module_runner_checks_local_sentences_against_visible_indexes() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            Arc::new(Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Int"),
                attributes: attrs(&[("token", json!(""))]),
            }),
            Arc::new(Sentence::SyntaxPriority {
                priorities: vec![vec!["high".into()], vec!["low".into()]],
                attributes: Attributes::default(),
            }),
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![
            Arc::new(production(
                Some("ordinary"),
                "Int",
                &[],
                Attributes::default(),
            )),
            Arc::new(Sentence::SyntaxAssociativity {
                associativity: Associativity::Left,
                tags: vec!["high".into(), "low".into()],
                attributes: Attributes::default(),
            }),
        ],
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 2);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<BTreeSet<_>>(),
        [
            DiagnosticCode::InvalidAssociativity,
            DiagnosticCode::InvalidTokenProduction,
        ]
        .into_iter()
        .collect()
    );
}

#[test]
fn module_runner_includes_term_structure_checks() {
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                Arc::new(Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: attrs(&[("token", json!(""))]),
                }),
                Arc::new(rule_with_body(token("0"))),
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidRewrite);
    assert_eq!(
        diagnostics[0].message,
        "Rules must have at least one rewrite."
    );
}

#[test]
fn as_patterns_require_variable_or_semantic_cast_aliases() {
    let invalid = rule_with_body(as_pattern(token("0"), token("1")));
    let variable = rule_with_body(as_pattern(token("0"), Term::variable("X")));
    let cast = rule_with_body(as_pattern(
        token("0"),
        Term::apply("#SemanticCastToInt", vec![Term::variable("X")]),
    ));
    let diagnostics = check_k_terms(&[&invalid, &variable, &cast]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidAsPattern);
    assert_eq!(
        diagnostics[0].message,
        "Found #as pattern where the right side is not a variable."
    );
}

#[test]
fn rewrite_check_matches_nested_missing_as_and_existential_cases() {
    let nested = rule_with_body(rewrite(
        rewrite(token("1"), token("2")),
        rewrite(token("3"), token("4")),
    ));
    let missing = rule_with_body(token("0"));
    let as_on_rhs = rule_with_body(rewrite(
        token("0"),
        as_pattern(token("1"), Term::variable("X")),
    ));
    let rewrite_inside_as = rule_with_body(as_pattern(
        rewrite(token("0"), token("1")),
        Term::variable("X"),
    ));
    let existential_on_lhs = rule_with_body(rewrite(Term::variable("?X"), token("0")));
    let diagnostics = check_rewrites(&[
        &nested,
        &missing,
        &as_on_rhs,
        &rewrite_inside_as,
        &existential_on_lhs,
    ]);

    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message == "Rewrites are not allowed to be nested.")
            .count(),
        2
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "Rules must have at least one rewrite." })
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "#as is not allowed in the RHS of a rule." })
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Rewrites are not allowed inside an #as pattern."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::InvalidExistentialVariable
            && diagnostic
                .message
                .starts_with("Existential variable ?X found in LHS")
    }));
}

#[test]
fn claims_need_no_rewrite_and_fun_expressions_do() {
    let claim = Sentence::Claim {
        body: token("0"),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let bad_fun = rule_with_body(rewrite(
        token("0"),
        Term::apply("#fun2", vec![token("1"), token("2")]),
    ));
    let good_fun = rule_with_body(rewrite(
        token("0"),
        Term::apply("#fun2", vec![rewrite(token("1"), token("2")), token("3")]),
    ));
    let diagnostics = check_rewrites(&[&claim, &bad_fun, &good_fun]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "#fun expressions must have at least one rewrite."
    );
}

#[test]
fn function_context_rejects_rewrites_and_nesting() {
    let context_rewrite = rule_with_body(Term::apply(
        "#withConfig",
        vec![token("0"), rewrite(token("1"), token("2"))],
    ));
    let nested_context = rule_with_body(Term::apply(
        "#withConfig",
        vec![
            token("0"),
            Term::apply("#withConfig", vec![token("1"), token("2")]),
        ],
    ));
    let context_in_rewrite = rule_with_body(rewrite(
        token("0"),
        Term::apply("#withConfig", vec![token("1"), token("2")]),
    ));
    let diagnostics = check_rewrites(&[&context_rewrite, &nested_context, &context_in_rewrite]);

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Rewrites are not allowed in the context of a function rule."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Function context is not allowed to be nested."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Function context is not allowed inside a rewrite."
    }));
}

#[test]
fn anonymous_check_warns_for_singletons_and_rejects_reused_named_underscores() {
    let sentence = Sentence::Rule {
        body: rewrite(
            Term::sequence([
                Term::variable("X"),
                Term::variable("_USED"),
                Term::variable("_"),
            ]),
            Term::sequence([Term::variable("_USED"), Term::variable("_")]),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: located(),
    };
    let diagnostics = check_anonymous_variables(&[&sentence]);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::UnusedVariable && diagnostic.message.contains("'X'")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::InvalidAnonymousVariable
            && diagnostic.message.contains("'_USED'")
    }));
}

#[test]
fn anonymous_check_preserves_context_exemptions_and_generated_suppression() {
    let context = Sentence::Context {
        body: Term::variable("HOLE"),
        requires: truth(),
        attributes: located(),
    };
    let alias = Sentence::ContextAlias {
        body: Term::sequence([Term::variable("HOLE"), Term::variable("HERE")]),
        requires: truth(),
        attributes: located(),
    };
    let generated = rule_with_body(Term::variable("GENERATED"));

    assert!(check_anonymous_variables(&[&context, &alias, &generated]).is_empty());
}

#[test]
fn rhs_check_reports_unbound_variables_and_preserves_fresh_exceptions() {
    let sentence = rule_with_body(rewrite(
        Term::variable("X"),
        Term::sequence([
            Term::variable("X"),
            Term::variable("Y"),
            Term::variable("?FRESH"),
            Term::variable("!CONSTANT"),
            Term::variable("THIS_CONFIGURATION"),
        ]),
    ));
    let diagnostics = check_rhs_variables(
        &[&sentence],
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    );

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::UnboundVariable);
    assert!(diagnostics[0].message.contains("variable Y"));
    assert!(diagnostics[0].message.contains("\"?Y\""));
}

#[test]
fn module_check_diagnostics_do_not_depend_on_declaration_order() {
    let unbound = |name: &str, line: u64| Sentence::Rule {
        body: rewrite(token("0"), Term::variable(name)),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            (SOURCE_ATTRIBUTE, json!("checks.k")),
            (LOCATION_ATTRIBUTE, json!([line, 1, line, 20])),
        ]),
    };
    let check = |sentences: Vec<Sentence>| {
        let resolved = resolved_definition(
            "MAIN",
            vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: sentences.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
        );
        check_module(&resolved, resolved.main_module_id()).unwrap()
    };

    let in_source_order = check(vec![unbound("A", 1), unbound("B", 2)]);
    let reversed = check(vec![unbound("B", 2), unbound("A", 1)]);

    assert_eq!(
        in_source_order
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::UnboundVariable)
            .count(),
        2,
        "{in_source_order:?}"
    );
    assert_eq!(in_source_order, reversed);
    assert!(in_source_order.windows(2).all(|pair| pair[0] <= pair[1]));
}

#[test]
fn unbound_variables_attribute_allows_named_exceptions() {
    let sentence = Sentence::Rule {
        body: rewrite(
            token("0"),
            Term::sequence([
                Term::variable("A"),
                Term::variable("B"),
                Term::variable("_"),
            ]),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("unboundVariables", json!(" A, B, _ "))]),
    };

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn requirements_bind_claim_and_symbolic_backend_variables_only() {
    let rule = Sentence::Rule {
        body: rewrite(token("0"), Term::variable("X")),
        requires: Term::variable("X"),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let claim = Sentence::Claim {
        body: rewrite(token("0"), Term::variable("X")),
        requires: Term::variable("X"),
        ensures: truth(),
        attributes: Attributes::default(),
    };

    let ordinary = check_rhs_variables(&[&rule], StructuralCheckOptions::default());
    let symbolic = check_rhs_variables(
        &[&rule],
        StructuralCheckOptions {
            backend: StructuralCheckBackend::Rust,
            ..StructuralCheckOptions::default()
        },
    );
    let claim = check_rhs_variables(&[&claim], StructuralCheckOptions::default());

    assert_eq!(ordinary.len(), 2);
    assert!(symbolic.is_empty());
    assert!(claim.is_empty());
}

#[test]
fn concrete_mode_rejects_each_existential_occurrence() {
    let sentence = rule_with_body(rewrite(
        Term::variable("?X"),
        Term::sequence([Term::variable("?X"), Term::variable("?Y")]),
    ));
    let concrete = check_rhs_variables(&[&sentence], StructuralCheckOptions::default());
    let symbolic = check_rhs_variables(
        &[&sentence],
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    );

    assert_eq!(
        concrete
            .iter()
            .filter(|diagnostic| {
                diagnostic.code == DiagnosticCode::UnsupportedExistentialVariable
            })
            .count(),
        3
    );
    assert!(symbolic.is_empty());
}

#[test]
fn ml_binders_bind_their_rhs_variables() {
    let sentence = rule_with_body(rewrite(
        token("0"),
        Term::apply(
            "#Exists",
            vec![
                Term::variable("X"),
                Term::apply("predicate", vec![Term::variable("X")]),
            ],
        ),
    ));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn variables_bind_by_name_across_differing_casts() {
    let sentence = rule_with_body(rewrite(
        Term::apply("#SemanticCastToBig", vec![Term::variable("X")]),
        Term::apply(
            "foo",
            vec![Term::apply(
                "#SemanticCastToSmall",
                vec![Term::variable("X")],
            )],
        ),
    ));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn variable_sort_annotations_do_not_affect_binding() {
    let typed = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Int")),
    };
    let cast = rule_with_body(rewrite(
        typed.clone(),
        Term::apply("#SemanticCastToInt", vec![Term::variable("X")]),
    ));
    let untyped = rule_with_body(rewrite(typed, Term::variable("X")));

    assert!(check_rhs_variables(&[&cast], StructuralCheckOptions::default()).is_empty());
    assert!(check_rhs_variables(&[&untyped], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn semantic_casts_supply_bound_variable_sort_context() {
    let cast = |name| Term::apply("#SemanticCastToInt", vec![Term::variable(name)]);
    let sentence = rule_with_body(rewrite(cast("X"), cast("X")));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn semantic_cast_context_does_not_override_nested_typed_variables() {
    let init = Term::Variable {
        name: "Init".into(),
        sort: Some(Sort::new("Map")),
    };
    let rhs = Term::apply(
        "#SemanticCastToK",
        vec![Term::apply(
            "project:KItem",
            vec![Term::apply("Map:lookup", vec![init.clone(), token("$PGM")])],
        )],
    );
    let sentence = rule_with_body(rewrite(init, rhs));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn rejects_fun_in_a_pattern_position_and_binds_the_variable_of_a_k_match() {
    let fun_pattern = rule_with_body(rewrite(
        Term::apply("#fun2", vec![rewrite(token("0"), token("1")), token("2")]),
        token("3"),
    ));
    let in_k = rule_with_body(rewrite(
        token("0"),
        Term::apply("_:=K_", vec![Term::variable("IGNORED"), token("1")]),
    ));
    let fun_diagnostics = check_rhs_variables(
        &[&fun_pattern],
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    );

    assert_eq!(fun_diagnostics.len(), 1);
    assert_eq!(
        fun_diagnostics[0].code,
        DiagnosticCode::InvalidFunctionPattern
    );
    assert!(check_rhs_variables(&[&in_k], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn context_alias_hole_is_the_only_unbound_context_exception() {
    let alias = Sentence::ContextAlias {
        body: rewrite(token("0"), Term::variable("HOLE")),
        requires: truth(),
        attributes: Attributes::default(),
    };
    let context = Sentence::Context {
        body: rewrite(token("0"), Term::variable("HOLE")),
        requires: truth(),
        attributes: Attributes::default(),
    };

    assert!(check_rhs_variables(&[&alias], StructuralCheckOptions::default()).is_empty());
    assert_eq!(
        check_rhs_variables(&[&context], StructuralCheckOptions::default()).len(),
        1
    );
}

#[test]
fn module_runner_options_control_existential_policy() {
    let sentence = rule_with_body(rewrite(token("0"), Term::variable("?X")));
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![sentence.into()],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let concrete = check_module(&resolved, resolved.main_module_id()).unwrap();
    let symbolic = check_module_with_options(
        &resolved,
        resolved.main_module_id(),
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    )
    .unwrap();

    assert!(
        concrete.iter().any(|diagnostic| {
            diagnostic.code == DiagnosticCode::UnsupportedExistentialVariable
        })
    );
    assert!(
        !symbolic.iter().any(|diagnostic| {
            diagnostic.code == DiagnosticCode::UnsupportedExistentialVariable
        })
    );
}

#[test]
fn functions_are_allowed_at_top_and_on_rhs_but_not_nested_on_lhs() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let wrapper = production(Some("wrap"), "Int", &["Int"], Attributes::default());
    let nested = rule_with_body(rewrite(
        Term::apply("wrap", vec![Term::apply("f", vec![token("0")])]),
        token("1"),
    ));
    let top = rule_with_body(rewrite(Term::apply("f", vec![token("0")]), token("1")));
    let rhs = rule_with_body(rewrite(
        Term::apply("wrap", vec![token("0")]),
        Term::apply("f", vec![token("1")]),
    ));
    let diagnostics = function_diagnostics(&[&nested, &top, &rhs], &[&function, &wrapper]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::IllegalFunctionOnLhs);
    assert!(diagnostics[0].message.contains("function symbol f"));
}

#[test]
fn simplification_rules_and_internal_labels_are_exempt() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let predicate = production(
        Some("isInt"),
        "Bool",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let wrapper = production(Some("wrap"), "Int", &["Int"], Attributes::default());
    let simplification = Sentence::Rule {
        body: rewrite(
            Term::apply("wrap", vec![Term::apply("f", vec![token("0")])]),
            token("1"),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("simplification", json!(""))]),
    };
    let internal = rule_with_body(rewrite(
        Term::apply("wrap", vec![Term::apply("isInt", vec![token("0")])]),
        token("1"),
    ));

    assert!(
        function_diagnostics(
            &[&simplification, &internal],
            &[&function, &predicate, &wrapper]
        )
        .is_empty()
    );
}

#[test]
fn collection_hooks_admit_functions_only_at_keys_set_elements_and_list_indices() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let map_element = production(
        Some("mapElement"),
        "Map",
        &["Int", "Int"],
        attrs(&[("function", json!("")), ("hook", json!("MAP.element"))]),
    );
    let set_element = production(
        Some("setElement"),
        "Set",
        &["Int"],
        attrs(&[("function", json!("")), ("hook", json!("SET.element"))]),
    );
    let list_update = production(
        Some("listUpdate"),
        "List",
        &["List", "Int", "Int"],
        attrs(&[("function", json!("")), ("hook", json!("LIST.update"))]),
    );
    let map_rule = rule_with_body(rewrite(
        Term::apply(
            "mapElement",
            vec![
                Term::apply("f", vec![token("0")]),
                Term::apply("f", vec![token("1")]),
            ],
        ),
        token("2"),
    ));
    let set_rule = rule_with_body(rewrite(
        Term::apply("setElement", vec![Term::apply("f", vec![token("0")])]),
        token("1"),
    ));
    let list_rule = rule_with_body(rewrite(
        Term::apply(
            "listUpdate",
            vec![
                Term::apply("f", vec![token("0")]),
                Term::apply("f", vec![token("1")]),
                Term::apply("f", vec![token("2")]),
            ],
        ),
        token("3"),
    ));
    let diagnostics = function_diagnostics(
        &[&map_rule, &set_rule, &list_rule],
        &[&function, &map_element, &set_element, &list_update],
    );

    assert_eq!(diagnostics.len(), 3);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| { diagnostic.code == DiagnosticCode::IllegalFunctionOnLhs })
    );
}

#[test]
fn with_config_keeps_its_first_argument_at_the_top_of_the_rule() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let sentence = rule_with_body(Term::apply(
        "#withConfig",
        vec![
            Term::apply("f", vec![token("0")]),
            Term::apply("f", vec![token("1")]),
        ],
    ));
    let diagnostics = function_diagnostics(&[&sentence], &[&function]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::IllegalFunctionOnLhs);
}

#[test]
fn module_runner_uses_visible_function_metadata() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            Arc::new(Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Int"),
                attributes: attrs(&[("token", json!(""))]),
            }),
            Arc::new(production(
                Some("f"),
                "Int",
                &["Int"],
                attrs(&[("function", json!(""))]),
            )),
            Arc::new(production(
                Some("wrap"),
                "Int",
                &["Int"],
                Attributes::default(),
            )),
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![Arc::new(rule_with_body(rewrite(
            Term::apply("wrap", vec![Term::apply("f", vec![token("0")])]),
            token("1"),
        )))],
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::IllegalFunctionOnLhs);
}

#[test]
fn strictness_checks_positions_semicolons_and_k_nonterminals() {
    let nullary = production(
        Some("nullary"),
        "Foo",
        &[],
        attrs(&[("strict", json!("1"))]),
    );
    let out_of_range = production(
        Some("unary"),
        "Foo",
        &["Foo"],
        attrs(&[("strict", json!("2"))]),
    );
    let bad_semicolons = production(
        Some("aliases"),
        "Foo",
        &["Foo"],
        attrs(&[("strict", json!("foo; bar; 1"))]),
    );
    let k_argument = production(Some("hot"), "Foo", &["K"], attrs(&[("strict", json!(""))]));
    let safe_argument = production(
        Some("safe"),
        "Foo",
        &["K", "KItem"],
        attrs(&[("strict", json!("2"))]),
    );
    let java_trailing_separators = production(
        Some("separator"),
        "Foo",
        &["K"],
        attrs(&[("strict", json!(";"))]),
    );
    let diagnostics = check_holes(&[
        &nullary,
        &out_of_range,
        &bad_semicolons,
        &k_argument,
        &safe_argument,
        &java_trailing_separators,
    ]);

    assert_eq!(diagnostics.len(), 4);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Cannot put a strict attribute on a production with no nonterminals"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message
            == "Expecting a number between 1 and 1, but found 2 as a strict position in [2]"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .starts_with("Invalid strict attribute containing invalid semicolons")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Cannot heat a nonterminal of sort K. Did you mean KItem?"
    }));
}

#[test]
fn contexts_reject_holes_cast_to_k_only() {
    let invalid = Sentence::Context {
        body: Term::apply("#SemanticCastToK", vec![Term::variable("HOLE")]),
        requires: truth(),
        attributes: Attributes::default(),
    };
    let valid = Sentence::Context {
        body: Term::apply("#SemanticCastToKItem", vec![Term::variable("HOLE")]),
        requires: truth(),
        attributes: Attributes::default(),
    };
    let diagnostics = check_holes(&[&invalid, &valid]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidHole);
}

#[test]
fn stream_cells_require_list_contents_and_valid_shape() {
    let valid = cell_production(
        "validStream",
        "ValidStreamCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("MyList"),
            name: None,
        },
        attrs(&[("cell", json!("")), ("stream", json!("stdin"))]),
    );
    let wrong_sort = cell_production(
        "badStream",
        "BadStreamCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("Int"),
            name: None,
        },
        attrs(&[("cell", json!("")), ("stream", json!("stdout"))]),
    );
    let malformed = cell_production(
        "malformedStream",
        "MalformedStreamCell",
        ProductionItem::Terminal("contents".into()),
        attrs(&[("cell", json!("")), ("stream", json!("stderr"))]),
    );
    let subsorts = PartialOrder::new([(Sort::new("MyList"), Sort::new("List"))]).unwrap();
    let diagnostics = check_streams(&[&valid, &wrong_sort, &malformed], &subsorts);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Wrong sort in streaming cell. Expected List, but found Int."
    }));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "Illegal arguments for stream cell." })
    );
}

#[test]
fn configuration_cells_detect_duplicates_and_unsupported_bags() {
    let child = cell_production(
        "kCell",
        "KCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("K"),
            name: None,
        },
        attrs(&[("cell", json!(""))]),
    );
    let first = cell_production(
        "topCell",
        "TopCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("KCell"),
            name: None,
        },
        attrs(&[("cell", json!(""))]),
    );
    let duplicate = cell_production(
        "otherCell",
        "OtherCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("KCell"),
            name: None,
        },
        attrs(&[("cell", json!(""))]),
    );
    let bag = cell_production(
        "bagCell",
        "BagCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("Int"),
            name: None,
        },
        attrs(&[("cell", json!("")), ("multiplicity", json!("*"))]),
    );
    let set = cell_production(
        "setCell",
        "SetCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("Int"),
            name: None,
        },
        attrs(&[
            ("cell", json!("")),
            ("multiplicity", json!("*")),
            ("type", json!("Set")),
        ]),
    );
    let production_catalog =
        ProductionCatalog::from_visible([&child, &first, &duplicate, &bag, &set]);
    let diagnostics =
        check_configuration_cells(&[&first, &duplicate, &bag, &set], &production_catalog);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::DuplicateConfigurationCell
            && diagnostic.message == "Cell kCell found twice in configuration."
    }));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == DiagnosticCode::UnsupportedCellBag })
    );
}

#[test]
fn module_runner_includes_production_shape_checks() {
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(production(
                Some("hot"),
                "Foo",
                &["K"],
                attrs(&[("strict", json!(""))]),
            ))],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidHole);
}

fn function_diagnostics(
    sentences: &[&Sentence],
    productions: &[&Sentence],
) -> Vec<k_rust::diagnostic::Diagnostic> {
    let production_catalog = ProductionCatalog::from_visible(productions.iter().copied());
    let sort_catalog = SortCatalog::from_visible(productions.iter().copied());
    check_functions(sentences, &production_catalog, &sort_catalog)
}

fn cell_production(
    label: &str,
    sort: &str,
    contents: ProductionItem,
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(label)),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: vec![
            ProductionItem::Terminal(format!("<{label}>")),
            contents,
            ProductionItem::Terminal(format!("</{label}>")),
        ],
        attributes,
    }
}

fn rule_with_body(body: Term) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    }
}

#[test]
fn klabel_checks_use_visible_productions_and_internal_labels() {
    let defined = production(Some("defined"), "Int", &[], Attributes::default());
    let parametric = Sentence::Production {
        label: Some(Label::with_parameters("parametric", vec![Sort::new("S")])),
        parameters: vec![Sort::new("S")],
        sort: Sort::new("S"),
        items: Vec::new(),
        attributes: Attributes::default(),
    };
    let missing = rule_with_body(rewrite(
        Term::Rewrite {
            left: Box::new(Term::apply("defined", Vec::new())),
            right: Box::new(Term::Apply {
                label: Label::with_parameters("parametric", vec![Sort::new("Int")]),
                arguments: Vec::new(),
            }),
        },
        Term::apply("missing", Vec::new()),
    ));
    let injected = rule_with_body(rewrite(
        Term::InjectedLabel(Label::new("alsoMissing")),
        Term::apply("isInt", vec![token("0")]),
    ));
    let claim = Sentence::Claim {
        body: rewrite(Term::apply("missingInClaim", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    // Compilation declares the generated counter cell, so a claim may name it before then.
    let counter_claim = Sentence::Claim {
        body: Term::apply(
            "<generatedCounter>",
            vec![rewrite(
                Term::variable("Counter"),
                Term::variable("NextCounter"),
            )],
        ),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let productions = ProductionCatalog::from_visible([&defined, &parametric]);
    let sorts = SortCatalog::from_visible([&defined, &parametric]);
    let diagnostics = check_klabels(
        &[&missing, &injected, &claim, &counter_claim],
        &productions,
        &sorts,
    );

    // A claim applying an undeclared label denotes nothing, exactly like a rule that does.
    assert_eq!(diagnostics.len(), 3);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == DiagnosticCode::UndefinedKLabel)
    );
    let mut messages = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    messages.sort_unstable();
    assert_eq!(
        messages,
        [
            "Found klabel alsoMissing not defined in any production.",
            "Found klabel missing not defined in any production.",
            "Found klabel missingInClaim not defined in any production.",
        ]
    );
}

#[test]
fn duplicate_klabels_are_scoped_to_the_main_import_closure() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            Arc::new(production(Some("dup"), "Int", &[], Attributes::default())),
            Arc::new(production(Some("#EmptyK"), "K", &[], Attributes::default())),
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![
            Arc::new(production(Some("dup"), "Other", &[], Attributes::default())),
            Arc::new(production(Some("#EmptyK"), "K", &[], Attributes::default())),
        ],
        attributes: Attributes::default(),
    };
    let disconnected = FlatModule {
        name: "DISCONNECTED".into(),
        imports: Vec::new(),
        local_sentences: vec![Arc::new(production(
            Some("dup"),
            "Elsewhere",
            &[],
            Attributes::default(),
        ))],
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![disconnected, main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_duplicate_klabels(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::DuplicateKLabel);
    assert!(diagnostics[0].message.contains("dup"));
}

#[test]
fn function_rules_must_consistently_use_concrete_or_symbolic() {
    let function = production(Some("f"), "Int", &[], attrs(&[("function", json!(""))]));
    let concrete = Sentence::Rule {
        body: rewrite(Term::apply("f", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!(""))]),
    };
    let ordinary = Sentence::Rule {
        body: rewrite(Term::apply("f", Vec::new()), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(function), Arc::new(concrete), Arc::new(ordinary)],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].code,
        DiagnosticCode::InconsistentFunctionRuleAttributes
    );
    assert!(diagnostics[0].message.contains("non-concrete rules"));
}

#[test]
fn function_rule_policy_covers_symbolic_conflicts_and_consistent_sets() {
    let symbolic_function = production(
        Some("symbolicF"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let conflicting_function = production(
        Some("conflictingF"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let consistent_function = production(
        Some("consistentF"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let symbolic = Sentence::Rule {
        body: rewrite(Term::apply("symbolicF", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("symbolic", json!(""))]),
    };
    let ordinary = Sentence::Rule {
        body: rewrite(Term::apply("symbolicF", Vec::new()), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let conflicting = Sentence::Rule {
        body: rewrite(Term::apply("conflictingF", Vec::new()), token("2")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!("")), ("symbolic", json!(""))]),
    };
    let consistent_one = Sentence::Rule {
        body: rewrite(Term::apply("consistentF", Vec::new()), token("3")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!(""))]),
    };
    let consistent_two = Sentence::Rule {
        body: rewrite(Term::apply("consistentF", Vec::new()), token("4")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!(""))]),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                Arc::new(symbolic_function),
                Arc::new(conflicting_function),
                Arc::new(consistent_function),
                Arc::new(symbolic),
                Arc::new(ordinary),
                Arc::new(conflicting),
                Arc::new(consistent_one),
                Arc::new(consistent_two),
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 2);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("non-symbolic rules"))
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Rule cannot be both concrete and symbolic in the same variable."
    }));
}

#[test]
fn simplification_rules_reject_overlapping_concrete_and_symbolic_variables() {
    let simplification = Sentence::Rule {
        body: rewrite(token("0"), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("simplification", json!("")),
            ("concrete", json!("X, Y")),
            ("symbolic", json!("Y, Z")),
        ]),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(simplification)],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Rule cannot be both concrete and symbolic in the same variable: [Y]"
    );
}

#[test]
fn bare_concrete_and_symbolic_on_a_simplification_rule_overlap_in_the_empty_name() {
    let simplification = Sentence::Rule {
        body: rewrite(token("0"), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("simplification", json!("")),
            ("concrete", json!("")),
            ("symbolic", json!("")),
        ]),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(simplification)],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Rule cannot be both concrete and symbolic in the same variable: []"
    );
}

#[test]
fn definition_runner_checks_every_module_and_definition_wide_invariants() {
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "BASE".into(),
                    public: true,
                }],
                local_sentences: vec![Arc::new(production(
                    Some("dup"),
                    "Int",
                    &[],
                    Attributes::default(),
                ))],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "BASE".into(),
                imports: Vec::new(),
                local_sentences: vec![
                    Arc::new(Sentence::SyntaxSort {
                        parameters: Vec::new(),
                        sort: Sort::new("K"),
                        attributes: Attributes::default(),
                    }),
                    Arc::new(production(Some("dup"), "Int", &[], Attributes::default())),
                    Arc::new(production(
                        Some("hot"),
                        "Foo",
                        &["K"],
                        attrs(&[("strict", json!(""))]),
                    )),
                ],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_definition(&resolved).unwrap();
    let codes = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<BTreeSet<_>>();

    assert!(codes.contains(&DiagnosticCode::DuplicateKLabel));
    assert!(codes.contains(&DiagnosticCode::InvalidHole));
}

#[test]
fn attribute_registry_rejects_unknown_and_misplaced_attributes() {
    let sentence = Sentence::Rule {
        body: rewrite(token("0"), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("binder", json!("")),
            ("made-up", json!("value")),
            ("label", json!("bad label`")),
            (SOURCE_ATTRIBUTE, json!("attributes.k")),
            (LOCATION_ATTRIBUTE, json!([4, 2, 4, 20])),
        ]),
    };
    let module = ResolvedModule {
        name: "MAIN".into(),
        local_sentences: vec![Arc::new(sentence)],
        attributes: attrs(&[("function", json!(""))]),
    };
    let diagnostics = check_attributes(&module);

    assert_eq!(diagnostics.len(), 4);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidAttribute)
            .count(),
        3
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::UnrecognizedAttribute
            && diagnostic.message.contains("made-up")
            && diagnostic.source.as_deref() == Some("attributes.k")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Label 'bad label`' cannot contain whitespace or backticks."
    }));
}

#[test]
fn format_checks_exempt_only_internal_layout_and_line_marker_sorts() {
    let regex_item = ProductionItem::regex(".+");
    let production = |sort: &str| Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: vec![regex_item.clone()],
        attributes: Attributes::default(),
    };
    let diagnostics = |sentence: &Sentence| {
        let productions = ProductionCatalog::from_visible([sentence]);
        let sorts = SortCatalog::from_visible([sentence]);
        check_attribute_semantics(&[sentence], &productions, &sorts)
    };

    assert!(diagnostics(&production("#Layout")).is_empty());
    assert!(diagnostics(&production("#LineMarker")).is_empty());
    assert!(diagnostics(&production("Layout")).iter().any(|diagnostic| {
        diagnostic
            .message
            .starts_with("Expected format attribute on production")
    }));
}

#[test]
fn rule_attribute_interactions_match_check_att() {
    let function = production(Some("f"), "Int", &[], attrs(&[("function", json!(""))]));
    let ordinary = production(Some("g"), "Int", &[], Attributes::default());
    let non_executable = Sentence::Rule {
        body: rewrite(Term::apply("g", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("non-executable", json!(""))]),
    };
    let simplification = Sentence::Rule {
        body: rewrite(Term::apply("f", Vec::new()), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("simplification", json!("")),
            ("owise", json!("")),
            ("priority", json!("50")),
            ("anywhere", json!("")),
            ("symbolic", json!("")),
        ]),
    };
    let syntactic = Sentence::Rule {
        body: rewrite(Term::apply("g", Vec::new()), token("2")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("syntactic", json!("X"))]),
    };
    let production_catalog = ProductionCatalog::from_visible([&function, &ordinary]);
    let sort_catalog = SortCatalog::from_visible([&function, &ordinary]);
    let diagnostics = check_attribute_semantics(
        &[&non_executable, &simplification, &syntactic],
        &production_catalog,
        &sort_catalog,
    );

    assert_eq!(diagnostics.len(), 6);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("non-executable attribute is only supported")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("anywhere attribute is not supported on symbolic rules")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("syntactic attribute is only supported")
    }));
}

#[test]
fn hooked_sort_binder_and_bracket_checks_use_visible_sort_metadata() {
    let hooked_sort = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Hooked"),
        attributes: attrs(&[("hook", json!("TEST.Hooked"))]),
    };
    let variable_sort = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Name"),
        attributes: attrs(&[("hook", json!("STRING.String"))]),
    };
    let hooked_constructor = production(Some("newHooked"), "Hooked", &[], Attributes::default());
    let binder = production(
        Some("bind"),
        "Expr",
        &["Name", "Expr"],
        attrs(&[("binder", json!(""))]),
    );
    let bracket = production(
        Some("bracket"),
        "Expr",
        &["Other"],
        attrs(&[("bracket", json!(""))]),
    );
    let visible = [
        &hooked_sort,
        &variable_sort,
        &hooked_constructor,
        &binder,
        &bracket,
    ];
    let production_catalog = ProductionCatalog::from_visible(visible);
    let sort_catalog = SortCatalog::from_visible(visible);
    let diagnostics = check_attribute_semantics(
        &[&hooked_constructor, &binder, &bracket],
        &production_catalog,
        &sort_catalog,
    );

    assert_eq!(diagnostics.len(), 3);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Cannot add new constructors to hooked sort Hooked")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("First child of binder must have a sort")
    }));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == DiagnosticCode::InvalidBracketProduction })
    );
}

#[test]
fn production_format_colors_and_deprecation_checks_report_each_defect() {
    let missing_format = Sentence::Production {
        label: Some(Label::new("regex")),
        parameters: Vec::new(),
        sort: Sort::new("Token"),
        items: vec![ProductionItem::regex("[a-z]+")],
        attributes: Attributes::default(),
    };
    let unfinished = Sentence::Production {
        label: Some(Label::new("unfinished")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![ProductionItem::Terminal("x".into())],
        attributes: attrs(&[("format", json!("%"))]),
    };
    let bad_index = Sentence::Production {
        label: Some(Label::new("badIndex")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![ProductionItem::Terminal("x".into())],
        attributes: attrs(&[("format", json!("%0"))]),
    };
    let regex_index = Sentence::Production {
        label: Some(Label::new("regexIndex")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![ProductionItem::regex("x")],
        attributes: attrs(&[("format", json!("%1"))]),
    };
    let colors = Sentence::Production {
        label: Some(Label::new("colors")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("Expr"),
                name: None,
            },
        ],
        attributes: attrs(&[("format", json!("%1%2")), ("colors", json!("red,blue"))]),
    };
    let deprecated = production(
        Some("legacy"),
        "Expr",
        &[],
        attrs(&[
            ("total", json!("")),
            ("terminator-symbol", json!(".Legacy")),
            ("functional", json!("")),
            ("latex", json!("legacy")),
        ]),
    );
    let visible = [
        &missing_format,
        &unfinished,
        &bad_index,
        &regex_index,
        &colors,
        &deprecated,
    ];
    let production_catalog = ProductionCatalog::from_visible(visible);
    let sort_catalog = SortCatalog::from_visible(visible);
    let diagnostics = check_attribute_semantics(&visible, &production_catalog, &sort_catalog);

    assert_eq!(diagnostics.len(), 9);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::DeprecatedAttribute)
            .count(),
        2
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Invalid format attribute: unfinished escape sequence."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Invalid colors attribute: expected 1")
    }));
}

#[test]
fn symbol_migration_and_overload_attributes_are_checked_together() {
    let legacy = production(
        Some("legacy"),
        "Expr",
        &[],
        attrs(&[("klabel", json!("legacy")), ("symbol", json!(""))]),
    );
    let conflicting = production(
        Some("conflicting"),
        "Expr",
        &[],
        attrs(&[
            ("klabel", json!("old")),
            ("symbol", json!("new")),
            ("overload", json!("group")),
        ]),
    );
    let unlabeled_overload = production(None, "Expr", &[], attrs(&[("overload", json!("group"))]));
    let visible = [&legacy, &conflicting, &unlabeled_overload];
    let production_catalog = ProductionCatalog::from_visible(visible);
    let sort_catalog = SortCatalog::from_visible(visible);
    let diagnostics = check_attribute_semantics(&visible, &production_catalog, &sort_catalog);

    assert_eq!(diagnostics.len(), 4);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Warning)
            .count(),
        1
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("cannot be combined with `klabel(_)`")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Production would not be a KORE symbol")
    }));
}

fn outer_check_module(name: &str, imports: &[&str], local_sentences: Vec<Sentence>) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: imports
            .iter()
            .map(|name| FlatImport {
                name: (*name).into(),
                public: true,
            })
            .collect(),
        local_sentences: local_sentences.into_iter().map(Arc::new).collect(),
        attributes: Attributes::default(),
    }
}

fn outer_check_diagnostics(main_module: &str, modules: Vec<FlatModule>) -> Vec<Diagnostic> {
    let definition = Definition {
        main_module: main_module.into(),
        modules,
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    check_definition(&resolved).unwrap()
}

fn outer_sort_diagnostics(diagnostics: &[Diagnostic]) -> Vec<&Diagnostic> {
    diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.message.starts_with("Could not find sorts:")
                || diagnostic
                    .message
                    .starts_with("User-defined parametric sorts are currently unsupported:")
                || diagnostic
                    .message
                    .starts_with("Nested parametric sorts are currently unsupported:")
                || diagnostic
                    .message
                    .starts_with("Parametric subsort declarations are currently unsupported:")
        })
        .collect()
}

fn syntax_sort(sort: Sort) -> Sentence {
    Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort,
        attributes: Attributes::default(),
    }
}

fn regex_token_production(sort: Sort, parameters: Vec<Sort>, regex: &str) -> Sentence {
    Sentence::Production {
        label: None,
        parameters,
        sort,
        items: vec![ProductionItem::RegexTerminal {
            regex: regex.into(),
            precede_regex: None,
            follow_regex: None,
        }],
        attributes: attrs(&[("token", json!(""))]),
    }
}

fn located_unused_symbol() -> Attributes {
    // These declaration-only fixtures intentionally never apply their symbols.
    let mut attributes = located();
    attributes.insert("unused", json!(""));
    attributes
}

#[test]
fn outer_checks_reject_a_token_production_at_its_own_sort_parameter() {
    let mut token = regex_token_production(Sort::new("S"), vec![Sort::new("S")], "[a-z]+@");
    *token.attributes_mut() = Attributes::merge([token.attributes(), &located()]).unwrap();
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module("MAIN", &[], vec![token.clone()])],
    );
    let diagnostics = k_rust::definition::check_outer_modules(&definition);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(
        diagnostics[0],
        Diagnostic::error(
            DiagnosticCode::InvalidTokenProduction,
            "A token production whose sort is its own sort parameter S gives every sort domain values, including every sort that has constructors, and a sort with domain values has no constructors; declare the token production at each sort that has these tokens",
            &token,
        )
    );
}

#[test]
fn outer_checks_reject_bare_parameter_sort_declarations_with_or_without_token() {
    for attributes in [Attributes::default(), attrs(&[("token", json!(""))])] {
        let mut declaration = Sentence::SyntaxSort {
            parameters: vec![Sort::new("S")],
            sort: Sort::new("S"),
            attributes,
        };
        *declaration.attributes_mut() =
            Attributes::merge([declaration.attributes(), &located()]).unwrap();
        let definition = resolved_definition(
            "MAIN",
            vec![outer_check_module("MAIN", &[], vec![declaration.clone()])],
        );
        let diagnostics = k_rust::definition::check_outer_modules(&definition);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0],
            Diagnostic::error(
                DiagnosticCode::UnsupportedParametricSort,
                "syntax {S} S declares no sort: S is a sort parameter of this declaration, so it names every sort, and the declaration's attributes would apply to all of them; declare each sort by name",
                &declaration,
            )
        );
    }
}

#[test]
fn constructor_schema_formals_do_not_refer_to_a_hooked_token_sort_of_the_same_name() {
    // The result and operand denote the sentence's formal, independently of its spelling.
    for formal in ["Int", "S"] {
        let mut schema = production(Some("wrap"), formal, &[formal], located_unused_symbol());
        let Sentence::Production { parameters, .. } = &mut schema else {
            unreachable!();
        };
        parameters.push(Sort::new(formal));
        let definition = resolved_definition(
            "MAIN",
            vec![
                outer_check_module(
                    "INT",
                    &[],
                    vec![
                        Sentence::SyntaxSort {
                            parameters: vec![],
                            sort: Sort::new("Int"),
                            attributes: attrs(&[("hook", json!("INT.Int")), ("token", json!(""))]),
                        },
                        regex_token_production(Sort::new("Int"), vec![], "[0-9]+"),
                    ],
                ),
                outer_check_module("MAIN", &["INT"], vec![schema]),
            ],
        );
        let diagnostics = check_definition(&definition).unwrap();
        assert!(diagnostics.is_empty(), "formal {formal}: {diagnostics:#?}");
    }
}

#[test]
fn constructors_at_instances_of_a_token_head_are_rejected_without_a_prelude() {
    let mut constructor = production(Some("foo"), "MInt", &[], located_unused_symbol());
    let Sentence::Production { sort, .. } = &mut constructor else {
        unreachable!();
    };
    *sort = mint(Sort::new("8"));
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                regex_token_production(mint(Sort::new("W")), vec![Sort::new("W")], "[0-9]+p[0-9]+"),
                constructor.clone(),
            ],
        )],
    );
    let diagnostics = check_definition(&definition).unwrap();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(
        diagnostics[0],
        Diagnostic::error(
            DiagnosticCode::InvalidTokenProduction,
            "Sort MInt{8} has domain values (its head has a token declaration, or the compiler writes its literals). Productions of this sort can only contain [function] or [token] labels.",
            &constructor,
        )
    );
}

#[test]
fn constructors_at_compiler_literal_sorts_are_rejected_without_a_token_declaration() {
    let constructor = production(Some("foo"), "Bool", &[], located_unused_symbol());
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module("MAIN", &[], vec![constructor.clone()])],
    );
    let diagnostics = check_definition(&definition).unwrap();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(
        diagnostics[0],
        Diagnostic::error(
            DiagnosticCode::InvalidTokenProduction,
            "Sort Bool has domain values (its head has a token declaration, or the compiler writes its literals). Productions of this sort can only contain [function] or [token] labels.",
            &constructor,
        )
    );
}

#[test]
fn constructors_at_exact_token_sorts_keep_the_existing_diagnostic_text() {
    let constructor = production(Some("foo"), "Int", &["Int"], located_unused_symbol());
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                regex_token_production(Sort::new("Int"), vec![], "[0-9]+"),
                constructor.clone(),
            ],
        )],
    );
    let diagnostics = check_definition(&definition).unwrap();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(
        diagnostics[0],
        Diagnostic::error(
            DiagnosticCode::InvalidTokenProduction,
            "Sort Int was declared as a token. Productions of this sort can only contain [function] or [token] labels.",
            &constructor,
        )
    );
}

#[test]
fn check_sorts_rejects_leading_zero_widths_without_undefined_sort_errors() {
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(mint(Sort::new("08"))),
                production(Some("eight"), "08", &[], Attributes::default()),
            ],
        )],
    );
    let (module_id, module) = definition.modules().next().unwrap();
    let diagnostics = k_rust::definition::check_sorts(module, &definition.sort_catalog(module_id));
    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    for diagnostic in diagnostics {
        assert_eq!(diagnostic.code, DiagnosticCode::InvalidNumeralSort);
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(
            diagnostic.message,
            "Sort 08 is a numeral written with a leading zero; a width is spelled 8."
        );
    }
}

#[test]
fn leading_zero_sort_diagnostics_cover_every_sentence_sort_depth_and_deduplicate() {
    let bad = Sort::new("08");
    let nested = mint(mint(bad.clone()));
    let operand = |sort| ProductionItem::NonTerminal { sort, name: None };
    let sentences = vec![
        Sentence::Production {
            label: Some(Label::new("repeated")),
            parameters: vec![bad.clone(), nested.clone()],
            sort: nested.clone(),
            items: vec![operand(bad.clone()), operand(nested.clone())],
            attributes: Attributes::default(),
        },
        Sentence::Production {
            label: Some(Label::new("result")),
            parameters: vec![],
            sort: nested.clone(),
            items: vec![ProductionItem::Terminal("result".into())],
            attributes: Attributes::default(),
        },
        Sentence::Production {
            label: Some(Label::new("operand")),
            parameters: vec![],
            sort: Sort::new("Foo"),
            items: vec![operand(nested.clone())],
            attributes: Attributes::default(),
        },
        Sentence::Production {
            label: Some(Label::new("parameter")),
            parameters: vec![nested.clone()],
            sort: Sort::new("Foo"),
            items: vec![ProductionItem::Terminal("parameter".into())],
            attributes: Attributes::default(),
        },
        syntax_sort(nested.clone()),
        Sentence::SyntaxSort {
            parameters: vec![nested.clone()],
            sort: Sort::new("Foo"),
            attributes: Attributes::default(),
        },
        Sentence::SortSynonym {
            new_sort: nested.clone(),
            old_sort: Sort::new("Foo"),
            attributes: Attributes::default(),
        },
        Sentence::SortSynonym {
            new_sort: Sort::new("Alias"),
            old_sort: nested.clone(),
            attributes: Attributes::default(),
        },
        Sentence::SortSynonym {
            new_sort: nested,
            old_sort: mint(Sort::new("0010")),
            attributes: Attributes::default(),
        },
    ];
    for (index, sentence) in sentences.into_iter().enumerate() {
        let definition = resolved_definition(
            "MAIN",
            vec![outer_check_module("MAIN", &[], vec![sentence])],
        );
        let (module_id, module) = definition.modules().next().unwrap();
        let diagnostics =
            k_rust::definition::check_sorts(module, &definition.sort_catalog(module_id));
        let numeral = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidNumeralSort)
            .collect::<Vec<_>>();
        let mut actual = numeral
            .iter()
            .map(|diagnostic| diagnostic.message.as_str())
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected =
            vec!["Sort 08 is a numeral written with a leading zero; a width is spelled 8."];
        if index == 8 {
            expected
                .push("Sort 0010 is a numeral written with a leading zero; a width is spelled 10.");
        }
        expected.sort();
        assert_eq!(actual, expected, "case {index}: {diagnostics:#?}");
        assert!(
            numeral
                .iter()
                .all(|diagnostic| diagnostic.severity == Severity::Error),
            "case {index}: {diagnostics:#?}"
        );
    }
}

#[test]
fn check_sorts_rejects_undefined_nonterminals_in_every_module() {
    let main_production = Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new("MainResult"),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("MissingMainSort"),
            name: None,
        }],
        attributes: attrs(&[
            (SOURCE_ATTRIBUTE, json!("main.k")),
            (LOCATION_ATTRIBUTE, json!([2, 3, 2, 40])),
        ]),
    };
    let unrelated_production = Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new("UnrelatedResult"),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("MissingUnrelatedSort"),
            name: None,
        }],
        attributes: attrs(&[
            (SOURCE_ATTRIBUTE, json!("unrelated.k")),
            (LOCATION_ATTRIBUTE, json!([7, 5, 7, 44])),
        ]),
    };
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![
            outer_check_module("MAIN", &[], vec![main_production]),
            outer_check_module("UNRELATED", &[], vec![unrelated_production]),
        ],
    );
    let diagnostics = outer_sort_diagnostics(&diagnostics);

    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Could not find sorts: [MissingMainSort]"
            && diagnostic.source.as_deref() == Some("main.k")
            && diagnostic
                .location
                .is_some_and(|location| location.start_line == 2)
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Could not find sorts: [MissingUnrelatedSort]"
            && diagnostic.source.as_deref() == Some("unrelated.k")
            && diagnostic
                .location
                .is_some_and(|location| location.start_line == 7)
    }));
}

#[test]
fn check_sorts_accepts_synonyms_and_declared_instantiations_but_rejects_a_parametric_subsort() {
    let formal = Sort::new("S");
    let mint_six = Sort::with_parameters("MInt", vec![Sort::new("6")]);
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                Sentence::SortSynonym {
                    new_sort: Sort::new("Alias"),
                    old_sort: Sort::new("Original"),
                    attributes: Attributes::default(),
                },
                syntax_sort(Sort::new("Original")),
                syntax_sort(mint_six.clone()),
                Sentence::Production {
                    label: None,
                    parameters: vec![formal.clone()],
                    sort: Sort::new("GenericResult"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: formal,
                        name: None,
                    }],
                    attributes: Attributes::default(),
                },
                production(None, "SynonymResult", &["Alias"], Attributes::default()),
                Sentence::Production {
                    label: None,
                    parameters: Vec::new(),
                    sort: Sort::new("InstantiatedResult"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: mint_six,
                        name: None,
                    }],
                    attributes: Attributes::default(),
                },
            ],
        )],
    );

    let errors = outer_sort_diagnostics(&diagnostics);
    assert_eq!(errors.len(), 1, "{diagnostics:#?}");
    assert_eq!(errors[0].code, DiagnosticCode::UnsupportedParametricSort);
    assert_eq!(
        errors[0].message,
        "Parametric subsort declarations are currently unsupported: GenericResult ::= S; declare the subsort of each instance instead",
    );
}

#[test]
fn check_sorts_finds_a_synonym_operand_by_its_denotation() {
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                Sentence::SortSynonym {
                    new_sort: Sort::new("Alias"),
                    old_sort: Sort::new("Original"),
                    attributes: Attributes::default(),
                },
                production(None, "SynonymResult", &["Alias"], Attributes::default()),
            ],
        )],
    );

    assert_eq!(
        outer_sort_diagnostics(&diagnostics)
            .iter()
            .map(|diagnostic| diagnostic.message.as_str())
            .collect::<Vec<_>>(),
        ["Could not find sorts: [Original]"]
    );
}

#[test]
fn check_sorts_rejects_a_synonym_as_a_sort_argument() {
    let mint = |argument| Sort::with_parameters("MInt", vec![Sort::new(argument)]);
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("Int")),
                Sentence::SortSynonym {
                    new_sort: Sort::new("Alias"),
                    old_sort: Sort::new("Int"),
                    attributes: Attributes::default(),
                },
                syntax_sort(mint("Alias")),
            ],
        )],
    );
    let sort_diagnostics = outer_sort_diagnostics(&diagnostics);
    assert_eq!(sort_diagnostics.len(), 1, "{diagnostics:#?}");
    assert!(
        sort_diagnostics[0]
            .message
            .starts_with("Could not find sorts: [Alias]")
    );
    assert!(sort_diagnostics[0].message.contains("sort synonym"));

    let control = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![syntax_sort(Sort::new("Int")), syntax_sort(mint("Int"))],
        )],
    );
    assert!(outer_sort_diagnostics(&control).is_empty(), "{control:#?}");
}

#[test]
fn check_sort_synonyms_reports_each_defect_once() {
    let synonym = |alias, referent| Sentence::SortSynonym {
        new_sort: Sort::new(alias),
        old_sort: Sort::new(referent),
        attributes: Attributes::default(),
    };
    let modules = vec![
        outer_check_module("CYC", &[], vec![synonym("A", "B"), synonym("B", "A")]),
        outer_check_module("USER", &["CYC"], vec![]),
        outer_check_module("L", &[], vec![synonym("X", "Int")]),
        outer_check_module("R", &[], vec![synonym("X", "Bool")]),
        outer_check_module("BOTH", &["L", "R"], vec![]),
        outer_check_module("TOP", &["USER", "BOTH"], vec![]),
    ];
    let resolved = resolved_definition("TOP", modules.clone());
    let diagnostics = k_rust::definition::check_sort_synonyms(&resolved);
    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == DiagnosticCode::InvalidSortSynonym)
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message.contains('A')
            && diagnostic.message.contains('B')
            && diagnostic.message.contains("cycle")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        ["X", "Int", "Bool", "BOTH"]
            .iter()
            .all(|name| diagnostic.message.contains(name))
    }));

    let compiled = k_rust::definition::check_definition_with_options(
        &resolved,
        k_rust::definition::StructuralCheckOptions::default(),
    )
    .unwrap();
    assert_eq!(
        compiled
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidSortSynonym)
            .count(),
        2,
        "{compiled:#?}"
    );

    let outer = outer_check_diagnostics("TOP", modules);
    assert_eq!(
        outer
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidSortSynonym)
            .count(),
        2
    );
    for diagnostic in diagnostics {
        assert_eq!(
            outer
                .iter()
                .filter(|candidate| *candidate == &diagnostic)
                .count(),
            1,
            "{outer:#?}"
        );
    }
}

fn overlap_synonym(alias: Sort, referent: Sort, source: &str, line: u32) -> Sentence {
    Sentence::SortSynonym {
        new_sort: alias,
        old_sort: referent,
        attributes: attrs(&[
            (SOURCE_ATTRIBUTE, json!(source)),
            (LOCATION_ATTRIBUTE, json!([line, 1, line, 20])),
        ]),
    }
}

#[test]
fn synonym_overlap_is_the_same_before_and_after_application_and_at_compile_checks() {
    let synonym = overlap_synonym(Sort::new("A"), Sort::new("T"), "main.k", 4);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            outer_check_module(
                "BASE",
                &[],
                vec![Sentence::Production {
                    label: Some(Label::new("a")),
                    parameters: vec![],
                    sort: Sort::new("A"),
                    items: vec![ProductionItem::Terminal("a".into())],
                    attributes: attrs(&[
                        (SOURCE_ATTRIBUTE, json!("base.k")),
                        (LOCATION_ATTRIBUTE, json!([2, 1, 2, 20])),
                        ("unused", json!("")),
                    ]),
                }],
            ),
            outer_check_module(
                "MAIN",
                &["BASE"],
                vec![
                    syntax_sort(Sort::new("T")),
                    synonym,
                    production(Some("use_alias"), "A", &[], located_unused_symbol()),
                ],
            ),
        ],
        attributes: Attributes::default(),
    };
    let raw = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    let applied = k_rust::definition::apply_sort_synonyms(&definition).unwrap();
    let applied = k_rust::definition::ResolvedDefinition::resolve(&applied).unwrap();
    let raw_overlap = k_rust::definition::check_sort_synonyms(&raw);
    assert_eq!(raw_overlap.len(), 1, "{raw_overlap:#?}");
    assert!(raw_overlap[0].message.contains("module MAIN:"));
    assert!(raw_overlap[0].message.contains("base.k:2"));
    assert_eq!(raw_overlap[0].source.as_deref(), Some("main.k"));
    assert_eq!(raw_overlap[0].location.unwrap().start_line, 4);
    assert_eq!(
        raw_overlap,
        k_rust::definition::check_sort_synonyms(&applied)
    );
    for definition in [&raw, &applied] {
        let compiled = check_definition(definition).unwrap();
        let overlap = compiled
            .into_iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidSortSynonym)
            .collect::<Vec<_>>();
        assert_eq!(overlap, raw_overlap);
    }
}

#[test]
fn synonym_overlap_compares_heads_by_name_and_arity() {
    let formal = Sort::new("W");
    let schema = Sentence::SyntaxSort {
        parameters: vec![formal.clone()],
        sort: Sort::with_parameters("MInt", vec![formal]),
        attributes: Attributes::default(),
    };
    let mint_eight = Sort::with_parameters("MInt", vec![Sort::new("8")]);
    for (alias, overlaps) in [(mint_eight, true), (Sort::new("MInt"), false)] {
        let synonym = overlap_synonym(alias, Sort::new("Foo"), "head.k", 3);
        let definition = resolved_definition(
            "MAIN",
            vec![outer_check_module(
                "MAIN",
                &[],
                vec![schema.clone(), syntax_sort(Sort::new("Foo")), synonym],
            )],
        );
        let diagnostics = k_rust::definition::check_sort_synonyms(&definition);
        assert_eq!(diagnostics.len(), usize::from(overlaps), "{diagnostics:#?}");
        if overlaps {
            assert!(diagnostics[0].message.contains("MInt{8}"));
            assert!(diagnostics[0].message.contains("MInt{W}"));
            assert_eq!(diagnostics[0].source.as_deref(), Some("head.k"));
            assert_eq!(diagnostics[0].location.unwrap().start_line, 3);
        }
    }
}

#[test]
fn synonym_overlap_deduplicates_repeated_declarations_and_importer_views() {
    let synonym = overlap_synonym(Sort::new("A"), Sort::new("T"), "synonym.k", 7);
    let mut declaration = syntax_sort(Sort::new("A"));
    *declaration.attributes_mut() = attrs(&[
        (SOURCE_ATTRIBUTE, json!("sort.k")),
        (LOCATION_ATTRIBUTE, json!([2, 1, 2, 20])),
    ]);
    let definition = resolved_definition(
        "TOP",
        vec![
            outer_check_module("B", &[], vec![declaration.clone(), declaration]),
            outer_check_module(
                "S",
                &[],
                vec![syntax_sort(Sort::new("T")), synonym.clone(), synonym],
            ),
            outer_check_module("FIRST", &["B", "S"], vec![]),
            outer_check_module("NEXT", &["B", "S"], vec![]),
            outer_check_module("TOP", &["FIRST", "NEXT"], vec![]),
        ],
    );
    let diagnostics = k_rust::definition::check_sort_synonyms(&definition);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    let first_combining = definition
        .dependency_order()
        .iter()
        .map(|&id| &definition.module(id).name)
        .find(|name| name.as_str() == "FIRST" || name.as_str() == "NEXT")
        .expect("the importers occur in dependency order");
    assert!(
        diagnostics[0]
            .message
            .contains(&format!("module {first_combining}:"))
    );
    assert!(diagnostics[0].message.contains("sort.k:2"));
    assert_eq!(diagnostics[0].source.as_deref(), Some("synonym.k"));
    assert_eq!(diagnostics[0].location.unwrap().start_line, 7);
}

#[test]
fn synonym_overlap_skips_undenoted_aliases_and_preserves_the_root_cycle_diagnostic() {
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("A")),
                overlap_synonym(Sort::new("A"), Sort::new("B"), "cycle.k", 3),
                overlap_synonym(Sort::new("B"), Sort::new("A"), "cycle.k", 4),
            ],
        )],
    );
    let diagnostics = k_rust::definition::check_sort_synonyms(&definition);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert!(diagnostics[0].message.contains("form a cycle"));
    assert!(!diagnostics[0].message.contains("second meaning"));
}

#[test]
fn synonym_overlap_rejects_the_rigid_sort_variable_and_leaves_numerals_to_their_check() {
    let rigid = resolved_definition(
        "RIGID",
        vec![outer_check_module(
            "RIGID",
            &[],
            vec![
                syntax_sort(Sort::new("Foo")),
                overlap_synonym(Sort::new("#SortParam"), Sort::new("Foo"), "rigid.k", 3),
            ],
        )],
    );
    let diagnostics = k_rust::definition::check_sort_synonyms(&rigid);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert!(
        diagnostics[0]
            .message
            .contains("#SortParam is the rigid sort variable")
    );
    assert_eq!(diagnostics[0].source.as_deref(), Some("rigid.k"));
    assert_eq!(diagnostics[0].location.unwrap().start_line, 3);

    let numeral = resolved_definition(
        "NUMERAL",
        vec![outer_check_module(
            "NUMERAL",
            &[],
            vec![
                syntax_sort(Sort::new("Foo")),
                overlap_synonym(Sort::new("8"), Sort::new("Foo"), "numeral.k", 3),
            ],
        )],
    );
    assert!(k_rust::definition::check_sort_synonyms(&numeral).is_empty());
    let diagnostics = k_rust::definition::check_outer_modules(&numeral);
    let errors = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1, "{diagnostics:#?}");
    assert_eq!(errors[0].code, DiagnosticCode::InvalidNumeralSort);
    assert_eq!(errors[0].source.as_deref(), Some("numeral.k"));
    assert_eq!(errors[0].location.unwrap().start_line, 3);
}

#[test]
fn check_sorts_rejects_undeclared_instantiations_and_parametric_results() {
    let formal = Sort::new("S");
    let mint_six = Sort::with_parameters("MInt", vec![Sort::new("6")]);
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                Sentence::Production {
                    label: None,
                    parameters: Vec::new(),
                    sort: Sort::new("UsesMInt"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: mint_six.clone(),
                        name: None,
                    }],
                    attributes: Attributes::default(),
                },
                Sentence::SyntaxSort {
                    parameters: vec![formal.clone()],
                    sort: Sort::with_parameters("Box", vec![formal.clone()]),
                    attributes: Attributes::default(),
                },
                Sentence::SortSynonym {
                    new_sort: Sort::with_parameters("Alias", vec![formal.clone()]),
                    old_sort: Sort::new("Original"),
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: None,
                    parameters: vec![formal.clone()],
                    sort: Sort::with_parameters("Wrapper", vec![formal]),
                    items: vec![ProductionItem::Terminal("wrap".into())],
                    attributes: Attributes::default(),
                },
            ],
        )],
    );
    let messages = outer_sort_diagnostics(&diagnostics)
        .into_iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<BTreeSet<_>>();

    assert_eq!(
        messages,
        BTreeSet::from([
            "Could not find sorts: [MInt{6}]",
            "User-defined parametric sorts are currently unsupported: Alias{S}",
            "User-defined parametric sorts are currently unsupported: Box{S}",
            "User-defined parametric sorts are currently unsupported: Wrapper{S}",
        ])
    );

    let accepted = outer_check_diagnostics(
        "MINT",
        vec![outer_check_module("MINT", &[], vec![syntax_sort(mint_six)])],
    );
    assert!(
        outer_sort_diagnostics(&accepted).is_empty(),
        "{accepted:#?}"
    );
}

fn mint(argument: Sort) -> Sort {
    Sort::with_parameters("MInt", vec![argument])
}

fn parametric_production(parameters: &[&str], sort: Sort, items: Vec<ProductionItem>) -> Sentence {
    Sentence::Production {
        label: None,
        parameters: parameters.iter().map(|name| Sort::new(*name)).collect(),
        sort,
        items,
        attributes: Attributes::default(),
    }
}

fn operand(sort: Sort) -> ProductionItem {
    ProductionItem::NonTerminal { sort, name: None }
}

#[test]
fn check_sorts_rejects_parametric_subsort_declarations_but_the_kernel_order_ones() {
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("Foo")),
                Sentence::SyntaxSort {
                    parameters: vec![Sort::new("W")],
                    sort: mint(Sort::new("W")),
                    attributes: Attributes::default(),
                },
                syntax_sort(mint(Sort::new("8"))),
                parametric_production(
                    &["W"],
                    Sort::new("Foo"),
                    vec![operand(mint(Sort::new("W")))],
                ),
                parametric_production(
                    &["S", "W"],
                    Sort::new("Foo"),
                    vec![operand(mint(Sort::new("W")))],
                ),
                parametric_production(&["S"], Sort::new("Foo"), vec![operand(Sort::new("S"))]),
                parametric_production(&["S"], Sort::new("S"), vec![operand(mint(Sort::new("S")))]),
            ],
        )],
    );
    let errors = outer_sort_diagnostics(&diagnostics);
    assert!(errors.iter().all(|diagnostic| {
        diagnostic.code == DiagnosticCode::UnsupportedParametricSort
            && diagnostic.severity == Severity::Error
    }));
    let mut messages = errors
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    messages.sort_unstable();
    assert_eq!(
        messages,
        vec![
            "Parametric subsort declarations are currently unsupported: Foo ::= MInt{W}; declare the subsort of each instance instead",
            "Parametric subsort declarations are currently unsupported: Foo ::= MInt{W}; declare the subsort of each instance instead",
            "Parametric subsort declarations are currently unsupported: Foo ::= S; declare the subsort of each instance instead",
            "Parametric subsort declarations are currently unsupported: S ::= MInt{S}; declare the subsort of each instance instead",
        ]
    );
}

#[test]
fn check_sorts_admits_kernel_order_and_labelled_parametric_productions() {
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("KBott")),
                Sentence::SyntaxSort {
                    parameters: vec![Sort::new("W")],
                    sort: mint(Sort::new("W")),
                    attributes: Attributes::default(),
                },
                syntax_sort(mint(Sort::new("8"))),
                parametric_production(&["S"], Sort::new("KItem"), vec![operand(Sort::new("S"))]),
                parametric_production(&["S"], Sort::new("S"), vec![operand(Sort::new("KBott"))]),
                Sentence::Production {
                    label: Some(Label::new("wrap")),
                    parameters: vec![Sort::new("S")],
                    sort: Sort::new("S"),
                    items: vec![
                        ProductionItem::Terminal("wrap(".into()),
                        operand(Sort::new("S")),
                        ProductionItem::Terminal(")".into()),
                    ],
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("inner")),
                    parameters: vec![Sort::new("T")],
                    sort: Sort::new("T"),
                    items: vec![
                        ProductionItem::Terminal("inner(".into()),
                        operand(mint(Sort::new("T"))),
                        ProductionItem::Terminal(")".into()),
                    ],
                    attributes: Attributes::default(),
                },
            ],
        )],
    );
    assert!(
        outer_sort_diagnostics(&diagnostics).is_empty(),
        "{diagnostics:#?}"
    );
}

#[test]
fn check_sorts_rejects_other_arities_nesting_and_undeclared_arguments_of_mint() {
    let (p, q, w) = (Sort::new("P"), Sort::new("Q"), Sort::new("W"));
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("A")),
                Sentence::SyntaxSort {
                    parameters: vec![p.clone(), q.clone()],
                    sort: Sort::with_parameters("MInt", vec![p, q]),
                    attributes: Attributes::default(),
                },
                syntax_sort(Sort::with_parameters(
                    "MInt",
                    vec![Sort::new("8"), Sort::new("16")],
                )),
                parametric_production(
                    &["W"],
                    mint(mint(w.clone())),
                    vec![ProductionItem::Terminal("mkn".into())],
                ),
                syntax_sort(mint(mint(Sort::new("8")))),
                parametric_production(&["W"], Sort::new("Uses"), vec![operand(mint(mint(w)))]),
                syntax_sort(mint(Sort::new("Undeclared"))),
            ],
        )],
    );
    let mut messages = outer_sort_diagnostics(&diagnostics)
        .into_iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    messages.sort_unstable();

    assert_eq!(
        messages,
        vec![
            "Could not find sorts: [Undeclared]",
            "Nested parametric sorts are currently unsupported: MInt{MInt{8}}",
            "Nested parametric sorts are currently unsupported: MInt{MInt{W}}",
            "Nested parametric sorts are currently unsupported: MInt{MInt{W}}",
            "Parametric subsort declarations are currently unsupported: Uses ::= MInt{MInt{W}}; declare the subsort of each instance instead",
            "User-defined parametric sorts are currently unsupported: MInt{8,16}",
            "User-defined parametric sorts are currently unsupported: MInt{P,Q}",
        ]
    );
}

#[test]
fn check_sorts_admits_mint_parameters_numerals_and_declared_arguments() {
    let a = Sort::new("A");
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(a.clone()),
                syntax_sort(mint(Sort::new("8"))),
                syntax_sort(mint(a)),
                Sentence::SyntaxSort {
                    parameters: vec![Sort::new("W")],
                    sort: mint(Sort::new("W")),
                    attributes: Attributes::default(),
                },
                parametric_production(
                    &["W"],
                    Sort::new("Uses"),
                    vec![
                        ProductionItem::Terminal("f".into()),
                        ProductionItem::Terminal("(".into()),
                        operand(mint(Sort::new("W"))),
                        ProductionItem::Terminal(")".into()),
                    ],
                ),
                parametric_production(
                    &["S"],
                    mint(Sort::new("S")),
                    vec![
                        ProductionItem::Terminal("wrap".into()),
                        ProductionItem::Terminal("(".into()),
                        operand(Sort::new("S")),
                        ProductionItem::Terminal(")".into()),
                    ],
                ),
                parametric_production(
                    &["T"],
                    Sort::new("T"),
                    vec![
                        ProductionItem::Terminal("inner".into()),
                        ProductionItem::Terminal("(".into()),
                        operand(mint(Sort::new("T"))),
                        ProductionItem::Terminal(")".into()),
                    ],
                ),
            ],
        )],
    );

    assert!(
        outer_sort_diagnostics(&diagnostics).is_empty(),
        "{diagnostics:#?}"
    );
}

fn user_list_at(source: &str, line: u32) -> Sentence {
    Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new("Elements"),
        items: vec![ProductionItem::Terminal(format!("separator-{line}"))],
        attributes: attrs(&[
            ("userList", json!("*")),
            (SOURCE_ATTRIBUTE, json!(source)),
            (LOCATION_ATTRIBUTE, json!([line, 3, line, 30])),
        ]),
    }
}

fn duplicate_user_list_diagnostics(diagnostics: &[Diagnostic]) -> Vec<&Diagnostic> {
    diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic
                .message
                .starts_with("Sort Elements previously declared as a user list at ")
        })
        .collect()
}

#[test]
fn check_user_lists_rejects_distinct_declarations_and_accepts_diamonds() {
    let imported_siblings = outer_check_diagnostics(
        "MAIN",
        vec![
            outer_check_module("A", &[], vec![user_list_at("lists.k", 2)]),
            outer_check_module("B", &[], vec![user_list_at("lists.k", 7)]),
            outer_check_module("MAIN", &["A", "B"], Vec::new()),
        ],
    );
    assert!(
        !duplicate_user_list_diagnostics(&imported_siblings).is_empty(),
        "{imported_siblings:#?}"
    );

    let local = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![user_list_at("local.k", 3), user_list_at("local.k", 4)],
        )],
    );
    assert!(
        duplicate_user_list_diagnostics(&local)
            .iter()
            .any(|diagnostic| {
                diagnostic.message.contains("Source(local.k)")
                    && diagnostic.message.contains("Location(3,3,3,30)")
                    && diagnostic.location.is_some()
            }),
        "{local:#?}"
    );

    let diamond = outer_check_diagnostics(
        "MAIN",
        vec![
            outer_check_module("BASE", &[], vec![user_list_at("base.k", 1)]),
            outer_check_module("LEFT", &["BASE"], Vec::new()),
            outer_check_module("RIGHT", &["BASE"], Vec::new()),
            outer_check_module("MAIN", &["LEFT", "RIGHT"], Vec::new()),
        ],
    );
    assert!(
        duplicate_user_list_diagnostics(&diamond).is_empty(),
        "{diamond:#?}"
    );

    let single = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![user_list_at("single.k", 1)],
        )],
    );
    assert!(
        duplicate_user_list_diagnostics(&single).is_empty(),
        "{single:#?}"
    );
}

#[test]
fn check_sorts_rejects_numeral_sorts_with_terms_or_positions() {
    let nt = |name| ProductionItem::NonTerminal {
        sort: Sort::new(name),
        name: None,
    };
    let terminal = |value: &str| ProductionItem::Terminal(value.into());
    let constructor = |parameters, sort, items| Sentence::Production {
        label: None,
        parameters,
        sort: Sort::new(sort),
        items,
        attributes: Attributes::default(),
    };
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("Foo")),
                constructor(vec![], "8", vec![terminal("eight")]),
                constructor(
                    vec![],
                    "Foo",
                    vec![terminal("bar"), terminal("("), nt("16"), terminal(")")],
                ),
                constructor(vec![], "Foo", vec![nt("32")]),
                constructor(vec![], "64", vec![nt("Foo")]),
                Sentence::SyntaxSort {
                    parameters: vec![],
                    sort: Sort::new("128"),
                    attributes: attrs(&[("token", json!(""))]),
                },
                Sentence::SyntaxSort {
                    parameters: vec![],
                    sort: Sort::new("256"),
                    attributes: attrs(&[("hook", json!("INT.Int"))]),
                },
                Sentence::SortSynonym {
                    new_sort: Sort::new("512"),
                    old_sort: Sort::new("Foo"),
                    attributes: Attributes::default(),
                },
                constructor(
                    vec![Sort::new("1024")],
                    "Foo",
                    vec![terminal("baz"), terminal("("), nt("1024"), terminal(")")],
                ),
            ],
        )],
    );
    let numeral = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidNumeralSort)
        .collect::<Vec<_>>();
    let mut messages = numeral
        .iter()
        .map(|diagnostic| diagnostic.message.clone())
        .collect::<Vec<_>>();
    messages.sort();
    let mut expected = [
        ("8", "the sort of a production"),
        ("16", "an operand of a production"),
        ("32", "an operand of a production"),
        ("64", "the sort of a production"),
        ("128", "a token or hooked sort"),
        ("256", "a token or hooked sort"),
        ("512", "a sort synonym"),
        ("1024", "a sort parameter"),
    ].map(|(sort, place)| format!("Sort {sort} is a numeral: it names a width, such as the argument of MInt{{{sort}}}, and has no terms, so it cannot be {place}."));
    expected.sort();
    assert_eq!(messages, expected);
    assert!(
        numeral
            .iter()
            .all(|diagnostic| diagnostic.severity == Severity::Error)
    );
    assert!(
        !diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.starts_with("Could not find sorts:")),
        "{diagnostics:#?}"
    );
}

#[test]
fn check_sorts_admits_numeral_declarations_arguments_and_synonym_targets() {
    let formal = Sort::new("S");
    let mint = |argument| Sort::with_parameters("MInt", vec![argument]);
    let diagnostics = outer_check_diagnostics(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("8")),
                syntax_sort(mint(Sort::new("8"))),
                syntax_sort(Sort::new("Foo")),
                Sentence::SortSynonym {
                    new_sort: Sort::new("W"),
                    old_sort: Sort::new("8"),
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("wrap")),
                    parameters: vec![formal.clone()],
                    sort: mint(formal.clone()),
                    items: vec![
                        ProductionItem::Terminal("wrap(".into()),
                        ProductionItem::NonTerminal {
                            sort: formal,
                            name: None,
                        },
                        ProductionItem::Terminal(")".into()),
                    ],
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("f")),
                    parameters: vec![],
                    sort: Sort::new("Foo"),
                    items: vec![
                        ProductionItem::Terminal("f(".into()),
                        ProductionItem::NonTerminal {
                            sort: mint(Sort::new("8")),
                            name: None,
                        },
                        ProductionItem::Terminal(")".into()),
                    ],
                    attributes: Attributes::default(),
                },
            ],
        )],
    );
    assert!(
        !diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == DiagnosticCode::InvalidNumeralSort),
        "{diagnostics:#?}"
    );
}

#[test]
fn numeral_sort_checks_use_operand_denotations_and_keep_one_error_per_place_and_sort() {
    let sentence = |parameters, sort, arguments: &[&str]| Sentence::Production {
        label: Some(Label::new("f")),
        parameters,
        sort: Sort::new(sort),
        items: arguments
            .iter()
            .map(|argument| ProductionItem::NonTerminal {
                sort: Sort::new(*argument),
                name: None,
            })
            .collect(),
        attributes: Attributes::default(),
    };
    let definition = resolved_definition(
        "MAIN",
        vec![outer_check_module(
            "MAIN",
            &[],
            vec![
                syntax_sort(Sort::new("Foo")),
                Sentence::SortSynonym {
                    new_sort: Sort::new("W"),
                    old_sort: Sort::new("8"),
                    attributes: Attributes::default(),
                },
                sentence(vec![], "16", &["W", "32", "W", "8"]),
                sentence(vec![Sort::new("64")], "64", &["64"]),
                Sentence::SyntaxSort {
                    parameters: vec![Sort::new("128")],
                    sort: Sort::new("128"),
                    attributes: attrs(&[("token", json!("")), ("hook", json!("INT.Int"))]),
                },
            ],
        )],
    );
    let (module_id, module) = definition.modules().next().unwrap();
    let diagnostics = k_rust::definition::check_sorts(module, &definition.sort_catalog(module_id));
    // A numeral formal is invalid because widths cannot be sort parameters.
    // Independently, binding the declaration's result declares no sort; the token/hook
    // attributes also require a sort with terms, which a width is not.
    assert_eq!(diagnostics.len(), 7, "{diagnostics:#?}");
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity == Severity::Error)
    );
    let mut expected = [
        ("16", "the sort of a production"),
        ("8", "an operand of a production"),
        ("32", "an operand of a production"),
        ("64", "a sort parameter"),
        ("128", "a sort parameter"),
        ("128", "a token or hooked sort"),
    ].map(|(sort, place)| (DiagnosticCode::InvalidNumeralSort, format!("Sort {sort} is a numeral: it names a width, such as the argument of MInt{{{sort}}}, and has no terms, so it cannot be {place}."))).to_vec();
    expected.push((
        DiagnosticCode::UnsupportedParametricSort,
        "syntax {128} 128 declares no sort: 128 is a sort parameter of this declaration, so it names every sort, and the declaration's attributes would apply to all of them; declare each sort by name".into(),
    ));
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| (diagnostic.code, diagnostic.message.clone()))
            .collect::<Vec<_>>(),
        expected
    );
}

fn collection_check_diagnostics(source: &str, main: &str) -> Vec<Diagnostic> {
    let parsed = k_rust::outer::parse("collections.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, main).unwrap();
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    check_module(&resolved, resolved.main_module_id()).unwrap()
}

fn collection_errors(diagnostics: &[Diagnostic], code: DiagnosticCode) -> Vec<&Diagnostic> {
    diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == code)
        .collect()
}

#[test]
fn collection_checks_reject_parametric_set_and_map_elements_at_their_productions() {
    for (main, source, element, hook) in [
        (
            "SET-ELEM-PARAM",
            r#"module SET-ELEM-PARAM
  syntax MySet [hook(SET.Set)]
  syntax {W} MySet ::= sitem(W) [function, hook(SET.element), symbol(sitem)]
  syntax MySet ::= ".MySet" [function, hook(SET.unit), symbol(sunit)]
  syntax MySet ::= MySet MySet [function, hook(SET.concat), symbol(sconcat), element(sitem), unit(sunit), assoc, comm, idem]
endmodule
"#,
            "sitem",
            "SET.element",
        ),
        (
            "MAP-PARAMETRIC",
            r#"module MAP-PARAMETRIC
  syntax V
  syntax MyMap [hook(MAP.Map)]
  syntax {W} MyMap ::= item(W, V) [function, hook(MAP.element), symbol(item)]
  syntax MyMap ::= ".MyMap" [function, hook(MAP.unit), symbol(unit)]
  syntax MyMap ::= MyMap MyMap [function, hook(MAP.concat), symbol(concat), element(item), unit(unit), assoc, comm]
  syntax {W} Bool ::= keys(W, MyMap) [function, hook(MAP.in_keys), symbol(keys)]
endmodule
"#,
            "item",
            "MAP.element",
        ),
        (
            "MAP-ELEM-ONLY",
            r#"module MAP-ELEM-ONLY
  syntax V
  syntax MyMap [hook(MAP.Map)]
  syntax {W} MyMap ::= item(W, V) [function, hook(MAP.element), symbol(item)]
  syntax MyMap ::= ".MyMap" [function, hook(MAP.unit), symbol(unit)]
  syntax MyMap ::= MyMap MyMap [function, hook(MAP.concat), symbol(concat), element(item), unit(unit), assoc, comm]
  syntax Bool ::= keys(V, MyMap) [function, hook(MAP.in_keys), symbol(keys)]
endmodule
"#,
            "item",
            "MAP.element",
        ),
    ] {
        let diagnostics = collection_check_diagnostics(source, main);
        let errors = collection_errors(&diagnostics, DiagnosticCode::UnsupportedParametricSort);
        let role = errors
            .iter()
            .find(|diagnostic| diagnostic.message.contains(hook))
            .unwrap_or_else(|| panic!("missing collection role rejection: {diagnostics:#?}"));
        assert!(role.message.contains(element) && role.message.contains("{W}"));
        assert_eq!(role.severity, Severity::Error);
        assert_eq!(role.source.as_deref(), Some("collections.k"));
        assert!(role.location.is_some(), "{role:#?}");
        assert!(
            errors
                .iter()
                .any(|diagnostic| diagnostic.message.contains("element attribute")),
            "{diagnostics:#?}"
        );
    }
}

#[test]
fn collection_checks_reject_every_parametric_hooked_role() {
    for hook in [
        "LIST.element",
        "LIST.concat",
        "LIST.unit",
        "SET.element",
        "SET.concat",
        "SET.unit",
        "MAP.element",
        "MAP.concat",
        "MAP.unit",
        "BAG.element",
        "BAG.concat",
        "BAG.unit",
        "RANGEMAP.elementRng",
        "RANGEMAP.concat",
        "RANGEMAP.unit",
    ] {
        let source = format!(
            "module ROLES syntax C syntax {{W}} C ::= role(W) [function, hook({hook}), symbol(role)] endmodule"
        );
        let diagnostics = collection_check_diagnostics(&source, "ROLES");
        let errors = collection_errors(&diagnostics, DiagnosticCode::UnsupportedParametricSort);
        assert_eq!(errors.len(), 1, "{hook}: {diagnostics:#?}");
        assert!(errors[0].message.contains(hook), "{diagnostics:#?}");
    }
}

#[test]
fn collection_checks_reject_schemas_named_by_collection_attributes() {
    for attribute in ["element", "update", "wrapElement"] {
        let source = format!(
            r#"module ATTRIBUTES
  syntax C
  syntax {{W}} C ::= role(W) [function, symbol(role)]
  syntax C ::= C "++" C [symbol(cat), {attribute}(role)]
endmodule"#
        );
        let diagnostics = collection_check_diagnostics(&source, "ATTRIBUTES");
        let errors = collection_errors(&diagnostics, DiagnosticCode::UnsupportedParametricSort);
        assert_eq!(errors.len(), 1, "{diagnostics:#?}");
        assert!(errors[0].message.contains(attribute) && errors[0].message.contains("role"));
        assert_eq!(errors[0].location.as_ref().unwrap().start_line, 4);
    }
}

#[test]
fn collection_checks_reject_schematic_units_of_collection_sorts() {
    for hook in [
        "MAP.Map",
        "SET.Set",
        "LIST.List",
        "BAG.Bag",
        "RANGEMAP.RangeMap",
    ] {
        let source = format!(
            r#"module UNIT-COLLECTION
  syntax C [hook({hook})]
  syntax {{S}} S ::= "eps" [symbol(eps)]
  syntax C ::= C "++" C [symbol(cat), unit(eps)]
endmodule"#
        );
        let diagnostics = collection_check_diagnostics(&source, "UNIT-COLLECTION");
        let errors = collection_errors(&diagnostics, DiagnosticCode::InvalidUnitAttribute);
        assert_eq!(errors.len(), 1, "{diagnostics:#?}");
        assert!(errors[0].message.contains(hook) && errors[0].message.contains("eps"));
        assert_eq!(errors[0].location.as_ref().unwrap().start_line, 4);
    }
}

#[test]
fn collection_checks_reject_units_with_unbound_sort_parameters() {
    let diagnostics = collection_check_diagnostics(
        r#"module UNIT-UNBOUND
  syntax Foo
  syntax {S} Foo ::= "eps" [symbol(eps)]
  syntax Foo ::= Foo "++" Foo [symbol(cat), unit(eps)]
endmodule"#,
        "UNIT-UNBOUND",
    );
    let errors = collection_errors(&diagnostics, DiagnosticCode::InvalidUnitAttribute);
    assert_eq!(errors.len(), 1, "{diagnostics:#?}");
    assert!(errors[0].message.contains("eps") && errors[0].message.contains("{S}"));
    assert_eq!(errors[0].location.as_ref().unwrap().start_line, 4);
}

#[test]
fn collection_checks_reject_in_keys_with_a_schematic_map_argument() {
    let diagnostics = collection_check_diagnostics(
        r#"module IN-KEYS
  syntax Bool
  syntax {W} Bool ::= keys(W, W) [function, hook(MAP.in_keys), symbol(keys)]
endmodule"#,
        "IN-KEYS",
    );
    let errors = collection_errors(&diagnostics, DiagnosticCode::UnsupportedParametricSort);
    assert_eq!(errors.len(), 1, "{diagnostics:#?}");
    assert!(errors[0].message.contains("MAP.in_keys") && errors[0].message.contains("keys"));
    assert_eq!(errors[0].location.as_ref().unwrap().start_line, 3);
}

#[test]
fn collection_checks_accept_parametric_list_operations_and_instantiable_units() {
    let diagnostics = collection_check_diagnostics(
        r#"module LIST-OPERATIONS
  syntax List [hook(LIST.List)]
  syntax Int
  syntax {W} MInt{W}
  syntax {W} List ::= update(List, Int, MInt{W}) [function, hook(LIST.updateMInt), symbol(update)]
  syntax {W} MInt{W} ::= get(List, Int) [function, hook(LIST.getMInt), symbol(get)]
  syntax {W} MInt{W} ::= size(List) [function, hook(LIST.sizeMInt), symbol(size)]
  syntax Foo
  syntax {S} S ::= "eps" [symbol(eps)]
  syntax Foo ::= Foo "++" Foo [symbol(cat), function, assoc, unit(eps)]
endmodule"#,
        "LIST-OPERATIONS",
    );
    assert!(
        collection_errors(&diagnostics, DiagnosticCode::UnsupportedParametricSort).is_empty(),
        "{diagnostics:#?}"
    );
    assert!(
        collection_errors(&diagnostics, DiagnosticCode::InvalidUnitAttribute).is_empty(),
        "{diagnostics:#?}"
    );
}

/// A constructor declared in a module that does not see its sort's hook or token declaration is
/// still a constructor of a sort with fixed values in the compiled definition, which the main
/// module's view decides: it is rejected wherever it is declared, once.
#[test]
fn constructors_are_judged_by_their_sort_in_the_main_modules_view() {
    let constructor = production(Some("x"), "Foo", &[], located_unused_symbol());
    let hooked = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Foo"),
        attributes: attrs(&[("hook", json!("BOOL.Bool"))]),
    };
    let token = regex_token_production(Sort::new("Foo"), vec![], "[0-9]+#");
    for (fixed, expected) in [
        (
            hooked,
            vec![(
                DiagnosticCode::InvalidAttribute,
                "Cannot add new constructors to hooked sort Foo",
            )],
        ),
        (
            token,
            vec![(
                DiagnosticCode::InvalidTokenProduction,
                "Sort Foo was declared as a token. Productions of this sort can only contain [function] or [token] labels.",
            )],
        ),
    ] {
        // The constructor's own module, a sibling of the fixing module, and the main module.
        for (constructor_module, main_sentences) in
            [("A", Vec::new()), ("MAIN", vec![constructor.clone()])]
        {
            let a_sentences = if constructor_module == "A" {
                vec![constructor.clone()]
            } else {
                Vec::new()
            };
            let definition = resolved_definition(
                "MAIN",
                vec![
                    outer_check_module("A", &[], a_sentences),
                    outer_check_module("B", &[], vec![fixed.clone()]),
                    outer_check_module("MAIN", &["A", "B"], main_sentences),
                ],
            );
            let diagnostics = check_definition(&definition).unwrap();
            let actual = diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .map(|diagnostic| (diagnostic.code, diagnostic.message.as_str()))
                .collect::<Vec<_>>();
            assert_eq!(
                actual, expected,
                "in {constructor_module}: {diagnostics:#?}"
            );
            assert!(
                diagnostics
                    .iter()
                    .all(|diagnostic| diagnostic.location.is_some()),
                "{diagnostics:#?}"
            );
        }
    }
}

/// A module the main module does not import contributes nothing to the compiled definition, so
/// its productions are judged in their own view only.
#[test]
fn constructors_outside_the_main_modules_imports_are_judged_in_their_own_view() {
    let constructor = production(Some("x"), "Foo", &[], located_unused_symbol());
    let hooked = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Foo"),
        attributes: attrs(&[("hook", json!("BOOL.Bool"))]),
    };
    let definition = resolved_definition(
        "MAIN",
        vec![
            outer_check_module("A", &[], vec![constructor]),
            outer_check_module("B", &["A"], vec![hooked]),
            outer_check_module("MAIN", &[], Vec::new()),
        ],
    );
    let diagnostics = check_definition(&definition).unwrap();
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity != Severity::Error),
        "{diagnostics:#?}"
    );
}

/// The compiled definition of a constructor on the hooked `MInt{A}` declared in an imported
/// module is rejected by the definition checks at the production, as it is in the main module,
/// instead of being emitted for the backend to refuse.
#[test]
fn a_constructor_on_a_hooked_instance_in_an_imported_module_is_rejected() {
    let source = "module MAIN-SYNTAX\n  syntax A\n  syntax MInt{A} ::= \"ka\" [symbol(ka)]\nendmodule\nmodule MAIN\n  imports MAIN-SYNTAX\nendmodule\n";
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let backend = k_rust::kompile::CompilationBackend::Rust;
    let loaded = k_rust::outer::load_with_options(
        k_rust::outer::ResolvedSource::new("main.k", source),
        "MAIN",
        &mut resolver,
        &k_rust::outer::LoadOptions {
            implicit_sources: vec![k_rust::builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
            ..k_rust::outer::LoadOptions::default()
        },
    )
    .expect("the definition loads");
    let error = k_rust::kompile::compile_loaded_definition(
        &loaded,
        k_rust::kompile::CompileOptions::default(),
    )
    .expect_err("the constructor is rejected");
    assert_eq!(error.stage, "definition checks");
    let rejection = error
        .diagnostics
        .iter()
        .find(|diagnostic| {
            diagnostic.message == "Cannot add new constructors to hooked sort MInt{A}"
        })
        .unwrap_or_else(|| panic!("{error:?}"));
    let location = rejection.location.expect("the diagnostic is located");
    assert_eq!(location.start_line, 3, "{rejection:?}");
}

fn definition_check_errors(source: &str, main: &str) -> Vec<Diagnostic> {
    let parsed = k_rust::outer::parse("compiled-view.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, main).unwrap();
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    check_definition(&resolved)
        .unwrap()
        .into_iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect()
}

/// A collection attribute names a symbol of the compiled definition, which may be declared in a
/// module the attribute's module does not import: the schema it names is rejected at the
/// attribute's production, once, as it is when both share a module.
#[test]
fn collection_attributes_are_judged_by_the_symbols_of_the_compiled_definition() {
    for attribute in ["element", "update", "wrapElement"] {
        let source = format!(
            r#"module A
  syntax C
  syntax C ::= C "++" C [function, symbol(cat), {attribute}(role)]
endmodule
module B
  syntax C
  syntax {{W}} C ::= role(W) [function, symbol(role)]
endmodule
module MAIN
  imports A
  imports B
endmodule"#
        );
        let errors = definition_check_errors(&source, "MAIN");
        assert_eq!(errors.len(), 1, "{attribute}: {errors:#?}");
        assert_eq!(errors[0].code, DiagnosticCode::UnsupportedParametricSort);
        assert!(
            errors[0].message.contains(attribute) && errors[0].message.contains("{W}"),
            "{errors:#?}"
        );
        assert_eq!(errors[0].location.as_ref().unwrap().start_line, 3);
    }

    // A unit whose sort parameters the result sort does not bind, declared in a sibling module.
    let errors = definition_check_errors(
        r#"module A
  syntax Foo
  syntax Foo ::= Foo "++" Foo [function, symbol(cat), unit(eps)]
endmodule
module B
  syntax Foo
  syntax {S} Foo ::= "eps" [symbol(eps)]
endmodule
module MAIN
  imports A
  imports B
endmodule"#,
        "MAIN",
    );
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert_eq!(errors[0].code, DiagnosticCode::InvalidUnitAttribute);
    assert!(errors[0].message.contains("{S}"), "{errors:#?}");
    assert_eq!(errors[0].location.as_ref().unwrap().start_line, 3);

    // A schematic unit of a sort whose collection hook a sibling module declares.
    let errors = definition_check_errors(
        r#"module A
  syntax C
  syntax {S} S ::= "eps" [symbol(eps)]
  syntax C ::= C "++" C [function, symbol(cat), unit(eps)]
endmodule
module B
  syntax C [hook(LIST.List)]
endmodule
module MAIN
  imports A
  imports B
endmodule"#,
        "MAIN",
    );
    let unit = errors
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidUnitAttribute)
        .collect::<Vec<_>>();
    assert_eq!(unit.len(), 1, "{errors:#?}");
    assert!(unit[0].message.contains("LIST.List"), "{errors:#?}");
    assert_eq!(unit[0].location.as_ref().unwrap().start_line, 4);
}

/// A module the main module does not import contributes nothing to the compiled definition, so
/// its collection attributes are judged in its own view, where the named schema is not visible.
#[test]
fn collection_attributes_outside_the_main_modules_imports_are_judged_in_their_own_view() {
    let errors = definition_check_errors(
        r#"module A
  syntax C
  syntax C ::= C "++" C [function, symbol(cat), element(role)]
endmodule
module B
  imports A
  syntax {W} C ::= role(W) [function, symbol(role)]
endmodule
module MAIN
  imports A
endmodule"#,
        "MAIN",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

/// Whether a sort lies below both `KList` and `Bag` is a property of the compiled definition's
/// subsort order, whichever module declares the subsorts: the sort is rejected at its
/// declaration as it is when one module declares all three.
#[test]
fn top_sorts_are_judged_by_the_subsorts_of_the_compiled_definition() {
    for (a, b) in [
        ("\n  syntax KList ::= Foo\n  syntax Bag ::= Foo", ""),
        ("", "\n  syntax KList ::= Foo\n  syntax Bag ::= Foo"),
        ("\n  syntax KList ::= Foo", "\n  syntax Bag ::= Foo"),
    ] {
        let source = format!(
            "module A\n  syntax Foo ::= \"x\" [symbol(x)]{a}\nendmodule\nmodule B\n  imports A{b}\nendmodule\nmodule MAIN\n  imports B\nendmodule"
        );
        let errors = definition_check_errors(&source, "MAIN");
        assert_eq!(errors.len(), 1, "{source}: {errors:#?}");
        assert_eq!(errors[0].code, DiagnosticCode::MultipleTopSorts);
        assert_eq!(errors[0].location.as_ref().unwrap().start_line, 2);
    }
}

/// Compile `source` (main and syntax module `MAIN`, no prelude) in process, as `kcompile
/// --no-prelude` does, and return the compilation error.
fn compile_error(source: &str) -> k_rust::kompile::CompileError {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let (loaded, _) = k_rust::outer::load_for_compilation(
        k_rust::outer::ResolvedSource::new("definition.k", source),
        "MAIN",
        Some("MAIN"),
        &mut resolver,
        &k_rust::outer::LoadOptions::default(),
    )
    .unwrap_or_else(|error| panic!("{source}\nthe source should load: {error:?}"));
    k_rust::kompile::compile_loaded_definition(&loaded, k_rust::kompile::CompileOptions::default())
        .expect_err(source)
}

/// The one error diagnostic of a compilation that the definition checks reject.
#[track_caller]
fn definition_check_error(source: &str) -> Diagnostic {
    let error = compile_error(source);
    assert_eq!(error.stage, "definition checks", "{source}\n{error:?}");
    let errors = error
        .diagnostics
        .into_iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    let [diagnostic] = <[Diagnostic; 1]>::try_from(errors)
        .unwrap_or_else(|errors| panic!("{source}\none error expected: {errors:#?}"));
    diagnostic
}

/// The prelude-free syntax the fresh-variable cases below share: `Int` tokens and the functions
/// their rules apply. A fresh value's sort needs no generator for these rejections.
const FRESH_CHECK_SYNTAX: &str = r#"
  syntax K
  syntax Bool
  syntax Int ::= r"[0-9]+" [token]
  syntax Int ::= plus(Int, Int) [function, symbol(plus)]
  syntax Bool ::= neq(Int, Int) [function, symbol(neq)] | gt(Int, Int) [function, symbol(gt)]"#;

/// Assert that `sentences`, written after [`FRESH_CHECK_SYNTAX`] in `MAIN`, are rejected with an
/// `InvalidFreshConstant` error for `!X` at the last sentence, column 3, whose message starts
/// with `message`.
#[track_caller]
fn assert_fresh_rejected(sentences: &str, message: &str) {
    let source = format!("module MAIN{FRESH_CHECK_SYNTAX}\n{sentences}\nendmodule\n");
    let error = compile_error(&source);
    assert_eq!(error.stage, "definition checks", "{source}\n{error:?}");
    // A claim in a definition is also rejected as such; the fresh variable is its own error.
    let fresh = error
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidFreshConstant)
        .collect::<Vec<_>>();
    let [diagnostic] = fresh.as_slice() else {
        panic!(
            "{source}\none fresh-variable error expected: {:#?}",
            error.diagnostics
        )
    };
    assert_eq!(diagnostic.severity, Severity::Error, "{source}");
    assert!(
        diagnostic.message.starts_with(message),
        "{source}\n{}",
        diagnostic.message
    );
    let line = 1 + FRESH_CHECK_SYNTAX.lines().count() + sentences.lines().count() - 1;
    let location = diagnostic.location.expect("the diagnostic is located");
    assert_eq!(
        (location.start_line, location.start_column),
        (line as u32, 3),
        "{source}"
    );
}

/// A fresh value is drawn from the configuration's counter cell by the rewrite step that
/// introduces it. Equations (function, simplification, anywhere, macro and alias rules) and
/// claims are applied without that cell, so a `!X` in them would be a variable nothing binds,
/// and each is rejected at its sentence, naming the kind of sentence.
#[test]
fn fresh_variables_outside_rewrite_steps_are_rejected_at_the_sentence() {
    for (sentences, kind) in [
        (
            "  syntax Int ::= g() [function]\n  rule g() => !X:Int",
            "a function rule",
        ),
        (
            "  syntax Int ::= g(Int) [function]\n  rule g(I) => I requires neq(I, !X:Int)",
            "a function rule",
        ),
        (
            "  syntax Int ::= g(Int) [function]\n  rule g(I) => plus(I, !X:Int) [simplification]",
            "a simplification rule",
        ),
        (
            "  syntax Foo ::= foo(Int)\n  rule foo(I) => foo(plus(I, !X:Int)) [anywhere]",
            "an anywhere rule",
        ),
        (
            "  syntax Int ::= \"m\" [macro]\n  rule m => !X:Int",
            "a macro or alias rule",
        ),
        (
            "  syntax Int ::= \"m\" [alias]\n  rule m => !X:Int",
            "a macro or alias rule",
        ),
        (
            "  syntax KItem ::= \"go\"\n  rule go => 1\n  claim go => !X:Int",
            "a claim",
        ),
    ] {
        assert_fresh_rejected(
            sentences,
            &format!("Fresh variable !X is not supported in {kind}:"),
        );
    }
}

/// The value of `!X` is allocated by the step that applies the rule, so it exists only in the
/// configuration after the step: the right-hand side of a rewrite and `ensures`. A context is
/// lowered to a heating step that builds its term and a cooling step that matches it again, so
/// `!X` has no place in it, the right-hand side of its rewrite included.
#[test]
fn fresh_variables_occur_only_where_a_rewrite_rule_builds_its_result() {
    for (sentences, place) in [
        (
            "  syntax KItem ::= foo(Int)\n  rule foo(!X:Int) => 1",
            "where a rule matches",
        ),
        (
            "  syntax KItem ::= foo(Int) | \"bar\"\n  configuration <k> bar </k>\n  rule <k> foo(!X:Int) => bar ...</k>",
            "where a rule matches",
        ),
        // Outside every rewrite the term is both matched and rebuilt.
        (
            "  syntax KItem ::= baz(Int, Int)\n  rule baz(!X:Int, I => plus(I, 1))",
            "where a rule matches",
        ),
        (
            "  syntax KItem ::= foo(Int) | \"bar\"\n  rule foo(I) => bar requires gt(!X:Int, I)",
            "in the requires clause of a rule",
        ),
    ] {
        assert_fresh_rejected(
            sentences,
            &format!("Fresh variable !X cannot occur {place}"),
        );
    }
    for context in ["pair(HOLE, !X:Int)", "pair(HOLE => tag(HOLE, !X:Int), _)"] {
        assert_fresh_rejected(
            &format!(
                "  syntax Exp ::= Int | pair(Exp, Exp) | tag(Exp, Int)\n  syntax KResult ::= Int\n  context {context}"
            ),
            "Fresh variable !X cannot occur in a context",
        );
    }
}

/// An anywhere rule applies to its left-hand side wherever that term occurs, with no
/// configuration around it: no parent cell to hold several sibling cells. The rule is rejected
/// at the rule by the definition checks, before any later stage looks for a production of the
/// cell sequence; the parent cell written around the same cells is a term, and compiles.
#[test]
fn anywhere_rules_needing_the_configuration_are_rejected_at_the_rule() {
    let diagnostic = definition_check_error(
        r#"module MAIN
  syntax K
  syntax Foo ::= "a" | "b"
  configuration <k> .K </k> <mem> a </mem>
  rule <k> .K </k> <mem> a => b </mem> [anywhere]
endmodule
"#,
    );
    assert_eq!(diagnostic.code, DiagnosticCode::InvalidAttribute);
    assert!(
        diagnostic
            .message
            .starts_with("An anywhere rule must rewrite a single term"),
        "{}",
        diagnostic.message
    );
    let location = diagnostic.location.expect("the diagnostic is located");
    assert_eq!((location.start_line, location.start_column), (5, 3));

    let source = r#"module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
  syntax Foo ::= "a" | "b"
  configuration <t> <k> .K </k> <mem> a </mem> </t>
  rule <t> <k> .K </k> <mem> a => b </mem> </t> [anywhere]
endmodule
"#;
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let (loaded, _) = k_rust::outer::load_for_compilation(
        k_rust::outer::ResolvedSource::new("definition.k", source),
        "MAIN",
        Some("MAIN"),
        &mut resolver,
        &k_rust::outer::LoadOptions::default(),
    )
    .unwrap();
    k_rust::kompile::compile_loaded_definition(&loaded, k_rust::kompile::CompileOptions::default())
        .expect("the parent cell makes the left-hand side one term");
}

/// An `overload(_)` attribute names the family of productions that overload one another; a
/// production whose family has no other member overloads nothing, which is worth a warning at
/// the production. The warning is a diagnostic like any other: under `--warnings-to-errors` it
/// fails the compilation at the post-compilation checks, and with warnings off it is not
/// reported at all. A family of two overloading productions is not reported. (The productions
/// are `unused` so that no other warning is promoted first.)
#[test]
fn singleton_overloads_are_warned_at_the_production_under_the_diagnostic_policy() {
    use k_rust::diagnostic::{DiagnosticPolicy, WarningLevel};
    let source = r#"module MAIN
  syntax K
  syntax Bool
  syntax Id ::= r"[a-z]+" [token]
  syntax LVal ::= "l" [symbol(l), unused]
                | LVal "." Id [symbol(lfield), overload(_.), unused]
  syntax Exp  ::= LVal
                | Exp "." Id [symbol(efield), overload(_._), unused]
  syntax Foo  ::= "foo" [symbol(foo), unused]
  syntax Foos ::= Foo
  syntax Bool ::= test(Foo) [function, symbol(testFoo), overload(test), unused]
                | test(Foos) [function, symbol(testFoos), overload(test), unused]
endmodule
"#;
    let compile = |diagnostics: DiagnosticPolicy| {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let (loaded, _) = k_rust::outer::load_for_compilation(
            k_rust::outer::ResolvedSource::new("definition.k", source),
            "MAIN",
            Some("MAIN"),
            &mut resolver,
            &k_rust::outer::LoadOptions::default(),
        )
        .unwrap();
        k_rust::kompile::compile_loaded_definition(
            &loaded,
            k_rust::kompile::CompileOptions {
                diagnostics,
                ..k_rust::kompile::CompileOptions::default()
            },
        )
    };
    let singletons = |diagnostics: &[Diagnostic], severity: Severity| {
        let mut lines = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::SingletonOverload)
            .map(|diagnostic| {
                assert_eq!(diagnostic.severity, severity, "{diagnostic:?}");
                assert_eq!(
                    diagnostic.message,
                    "Production has an `overload(_)` attribute but is not an overload of any other production."
                );
                diagnostic.location.expect("located").start_line
            })
            .collect::<Vec<_>>();
        lines.sort_unstable();
        lines
    };

    let normal = compile(DiagnosticPolicy::default()).expect("a warning does not fail");
    assert_eq!(singletons(&normal.diagnostics, Severity::Warning), [6, 8]);

    let promoted = compile(DiagnosticPolicy {
        level: WarningLevel::All,
        warnings_to_errors: true,
    })
    .expect_err("promoted warnings fail the compilation");
    assert_eq!(promoted.stage, "post-compilation checks", "{promoted:#?}");
    assert_eq!(singletons(&promoted.diagnostics, Severity::Error), [6, 8]);

    let suppressed = compile(DiagnosticPolicy {
        level: WarningLevel::None,
        warnings_to_errors: true,
    })
    .expect("suppressed warnings are not promoted");
    assert_eq!(
        singletons(&suppressed.diagnostics, Severity::Warning),
        [0; 0]
    );
}
