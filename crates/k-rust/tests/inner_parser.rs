use k_rust::definition::{Associativity, Attributes, ProductionItem, Sentence};
use k_rust::inner::{Grammar, ParseError};
use k_rust::kast::{Label, Sort, Term};

macro_rules! assert_inner_parse_snapshot {
    ($grammar:expr, $sort:expr, $source:expr) => {{
        let source = indoc::indoc! { $source };
        let expected_sort = $sort;
        let parsed = $grammar.parse(&expected_sort, source);
        insta::with_settings!({
            description => format!("Input parsed as {expected_sort}:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(parsed);
        });
    }};
}

fn production(
    result: &str,
    items: Vec<ProductionItem>,
    label: Option<&str>,
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: label.map(Label::new),
        parameters: vec![],
        sort: Sort::new(result),
        items,
        attributes,
    }
}

fn nonterminal(sort: &str) -> ProductionItem {
    ProductionItem::NonTerminal {
        sort: Sort::new(sort),
        name: None,
    }
}

fn precedence(value: &str) -> Attributes {
    let mut attributes = Attributes::default();
    attributes.insert("prec", serde_json::json!(value));
    attributes
}

fn syntax_sort(sort: &str) -> Sentence {
    Sentence::SyntaxSort {
        parameters: vec![],
        sort: Sort::new(sort),
        attributes: Attributes::default(),
    }
}

#[test]
fn parses_recursive_grammars_tokens_subsorts_and_layout() {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    let mut bracket_attributes = Attributes::default();
    bracket_attributes.insert("bracket", serde_json::json!(""));
    let sentences = vec![
        production(
            "Id",
            vec![ProductionItem::regex("[a-z]+")],
            None,
            token_attributes,
        ),
        production("Exp", vec![nonterminal("Id")], None, Attributes::default()),
        production(
            "Exp",
            vec![
                ProductionItem::Terminal("(".into()),
                nonterminal("Exp"),
                ProductionItem::Terminal(")".into()),
            ],
            None,
            bracket_attributes,
        ),
        production(
            "Exp",
            vec![
                nonterminal("Exp"),
                ProductionItem::Terminal("+".into()),
                nonterminal("Exp"),
            ],
            Some("plus"),
            Attributes::default(),
        ),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    assert_eq!(
        grammar
            .parse(&Sort::new("Exp"), " /* left */ (foo) + bar // tail")
            .unwrap(),
        Term::apply(
            "plus",
            vec![
                Term::Token {
                    token: "foo".into(),
                    sort: Sort::new("Id"),
                },
                Term::Token {
                    token: "bar".into(),
                    sort: Sort::new("Id"),
                },
            ],
        )
    );
}

fn layout_start_production() -> Sentence {
    production(
        "Start",
        vec![ProductionItem::Terminal("x".into())],
        Some("x"),
        Attributes::default(),
    )
}

fn custom_layout_grammar() -> Grammar {
    let start = layout_start_production();
    Grammar::from_sentences(&[
        start,
        Sentence::SyntaxLexical {
            name: "Gap".into(),
            regex: "[ _]".into(),
            attributes: Attributes::default(),
        },
        production(
            "#Layout",
            vec![ProductionItem::regex("{Gap}+")],
            None,
            Attributes::default(),
        ),
        production(
            "#Layout",
            vec![ProductionItem::regex("~+")],
            None,
            Attributes::default(),
        ),
    ])
    .unwrap()
}

fn disabled_layout_grammar() -> Grammar {
    Grammar::from_sentences(&[layout_start_production(), syntax_sort("#Layout")]).unwrap()
}

#[test]
fn uses_default_layout_when_layout_is_undeclared() {
    let grammar = Grammar::from_sentences([&layout_start_production()]).unwrap();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), " /* default */ x // tail");
}

#[test]
fn uses_module_defined_layout() {
    let grammar = custom_layout_grammar();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "~~ _ x~~~");
}

#[test]
fn module_defined_layout_rejects_default_comments() {
    let grammar = custom_layout_grammar();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "/* not custom */ x");
}

#[test]
fn production_free_layout_allows_adjacent_tokens() {
    let grammar = disabled_layout_grammar();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "x");
}

#[test]
fn production_free_layout_rejects_whitespace() {
    let grammar = disabled_layout_grammar();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), " x");
}

#[test]
fn rejects_non_regex_layout_productions() {
    let start = production(
        "#Layout",
        vec![ProductionItem::Terminal(" ".into())],
        None,
        Attributes::default(),
    );
    assert_eq!(
        Grammar::from_sentences(&[syntax_sort("#Layout"), start]).unwrap_err(),
        ParseError::InvalidLayoutProduction
    );
}

#[test]
fn rejects_empty_matching_layout_regexes() {
    let sentences = [
        syntax_sort("#Layout"),
        production(
            "#Layout",
            vec![ProductionItem::regex("a*")],
            None,
            Attributes::default(),
        ),
    ];
    assert_eq!(
        Grammar::from_sentences(&sentences).unwrap_err(),
        ParseError::EmptyLayout
    );
}

#[test]
fn preserves_nullable_derivations() {
    let sentences = vec![
        production(
            "Start",
            vec![nonterminal("Empty"), ProductionItem::Terminal("x".into())],
            Some("start"),
            Attributes::default(),
        ),
        production(
            "Empty",
            vec![ProductionItem::Terminal(String::new())],
            Some("empty"),
            Attributes::default(),
        ),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    assert_eq!(
        grammar.parse(&Sort::new("Start"), "x").unwrap(),
        Term::apply("start", vec![Term::apply("empty", vec![])])
    );
}

#[test]
fn prediction_reuse_completes_early_and_late_nullable_callers() {
    let sentences = vec![
        production(
            "Start",
            vec![
                nonterminal("Empty"),
                ProductionItem::Terminal("early".into()),
            ],
            Some("early"),
            Attributes::default(),
        ),
        production(
            "Start",
            vec![
                nonterminal("Prefix"),
                nonterminal("Empty"),
                ProductionItem::Terminal("late".into()),
            ],
            Some("late"),
            Attributes::default(),
        ),
        production("Empty", vec![], Some("empty"), Attributes::default()),
        production(
            "Prefix",
            vec![nonterminal("Unit")],
            Some("prefix"),
            Attributes::default(),
        ),
        production("Unit", vec![], Some("unit"), Attributes::default()),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();
    // Empty finishes before Prefix creates the second caller waiting for Empty.
    assert_eq!(
        grammar.parse(&Sort::new("Start"), "late").unwrap(),
        Term::apply(
            "late",
            vec![
                Term::apply("prefix", vec![Term::apply("unit", vec![])]),
                Term::apply("empty", vec![])
            ]
        ),
    );
    assert_eq!(
        grammar.parse(&Sort::new("Start"), "early").unwrap(),
        Term::apply("early", vec![Term::apply("empty", vec![])]),
    );
}

#[test]
#[cfg(feature = "z3-inference")]
fn prediction_reuse_propagates_later_nullable_alternatives() {
    let sentences = vec![
        production(
            "Start",
            vec![nonterminal("Empty"), ProductionItem::Terminal("ok".into())],
            Some("start"),
            Attributes::default(),
        ),
        production("Empty", vec![], Some("early"), Attributes::default()),
        production(
            "Empty",
            vec![nonterminal("Unit")],
            Some("late"),
            Attributes::default(),
        ),
        production("Unit", vec![], Some("unit"), Attributes::default()),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();
    let ParseError::Ambiguous {
        parses,
        alternatives,
        ..
    } = grammar.parse(&Sort::new("Start"), "ok").unwrap_err()
    else {
        panic!("both nullable derivations must survive");
    };
    assert_eq!(parses, 2);
    assert_eq!(
        alternatives
            .into_iter()
            .map(|alternative| alternative.term)
            .collect::<Vec<_>>(),
        vec![
            Term::apply("early", vec![]).to_string(),
            Term::apply("late", vec![Term::apply("unit", vec![])]).to_string()
        ],
    );
}

#[test]
#[cfg(feature = "z3-inference")]
fn prediction_reuse_distinguishes_full_parameterized_sorts() {
    let mut sentences = Vec::new();
    for (parameter, suffix) in [("Int", "bad"), ("Bool", "ok")] {
        let sort = Sort::with_parameters("Box", vec![Sort::new(parameter)]);
        sentences.push(production(
            "Start",
            vec![
                ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                },
                ProductionItem::Terminal(suffix.into()),
            ],
            Some(suffix),
            Attributes::default(),
        ));
        sentences.push(Sentence::Production {
            label: Some(Label::new(parameter)),
            parameters: vec![],
            sort,
            items: vec![ProductionItem::Terminal("x".into())],
            attributes: Attributes::default(),
        });
    }
    let grammar = Grammar::from_sentences(&sentences).unwrap();
    for (parameter, suffix) in [("Bool", "ok"), ("Int", "bad")] {
        assert_eq!(
            grammar
                .parse(&Sort::new("Start"), &format!("x {suffix}"))
                .unwrap(),
            Term::apply(suffix, vec![Term::apply(parameter, vec![])]),
        );
    }
}

#[test]
fn prediction_reuse_preserves_layout_positions_provenance_and_rejection() {
    use k_rust::kast::{ResolvedProductionId, TermSpan};
    use k_rust::provenance::SourceId;

    let sentences = vec![
        production(
            "Start",
            vec![
                nonterminal("Empty"),
                ProductionItem::Terminal("x".into()),
                nonterminal("Empty"),
                ProductionItem::Terminal("x".into()),
                nonterminal("Empty"),
            ],
            Some("start"),
            Attributes::default(),
        ),
        production("Empty", vec![], Some("empty"), Attributes::default()),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();
    let input = " \tx \n x // tail";
    let source = SourceId(7);
    let offset = 100;
    let parsed = grammar
        .parse_with_provenance(&Sort::new("Start"), input, source, offset)
        .unwrap();
    let Term::Apply { arguments, .. } = parsed.unannotated() else {
        panic!("expected the start constructor");
    };
    assert_eq!(arguments.len(), 3);
    for (child, position) in arguments.iter().zip([
        input.find('x').unwrap(),
        input.rfind('x').unwrap(),
        input.len(),
    ]) {
        let metadata = child.metadata().expect("nullable child retains metadata");
        assert_eq!(
            metadata.span,
            Some(TermSpan {
                source,
                start: offset + position,
                end: offset + position
            })
        );
        assert_eq!(metadata.production, Some(ResolvedProductionId(1)));
    }
    assert_eq!(
        grammar.parse(&Sort::new("Start"), "x y"),
        Err(ParseError::NoParse {
            position: 2,
            expected: vec!["\"x\"".into(), "Empty".into()]
        }),
    );
}

#[test]
fn reports_real_tree_ambiguity() {
    let sentences = vec![
        production(
            "Start",
            vec![ProductionItem::Terminal("x".into())],
            Some("first"),
            Attributes::default(),
        ),
        production(
            "Start",
            vec![ProductionItem::Terminal("x".into())],
            Some("second"),
            Attributes::default(),
        ),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    #[cfg(feature = "z3-inference")]
    assert!(matches!(
        grammar.parse(&Sort::new("Start"), "x"),
        Err(ParseError::Ambiguous { alternatives, .. }) if alternatives.len() == 2
    ));
    #[cfg(not(feature = "z3-inference"))]
    assert_eq!(
        grammar.parse(&Sort::new("Start"), "x"),
        Err(ParseError::Z3InferenceRequired {
            ambiguity: true,
            parametric_sorts: false,
        })
    );
}

#[test]
fn expands_named_lexical_references() {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    let sentences = vec![
        Sentence::SyntaxLexical {
            name: "Digit".into(),
            regex: "[0-9]".into(),
            attributes: Attributes::default(),
        },
        production(
            "Int",
            vec![ProductionItem::regex("{Digit}+")],
            None,
            token_attributes,
        ),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    assert_eq!(
        grammar.parse(&Sort::new("Int"), "123").unwrap(),
        Term::Token {
            token: "123".into(),
            sort: Sort::new("Int"),
        }
    );
}

#[test]
fn scanner_prefers_the_longer_terminal() {
    let grammar = Grammar::from_sentences(&[
        production(
            "Start",
            vec![
                ProductionItem::Terminal("=".into()),
                ProductionItem::Terminal("=".into()),
            ],
            Some("split"),
            Attributes::default(),
        ),
        production(
            "Start",
            vec![ProductionItem::Terminal("==".into())],
            Some("longTerminal"),
            Attributes::default(),
        ),
    ])
    .unwrap();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "==");
}

#[test]
fn scanner_prefers_a_literal_on_an_equal_length_match() {
    let grammar = Grammar::from_sentences(&[
        production(
            "Start",
            vec![ProductionItem::regex("[a-z]+")],
            Some("identifier"),
            Attributes::default(),
        ),
        production(
            "Start",
            vec![ProductionItem::Terminal("if".into())],
            Some("keyword"),
            Attributes::default(),
        ),
    ])
    .unwrap();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "if");
}

#[test]
fn scanner_uses_precedence_to_break_equal_length_regex_ties() {
    let grammar = Grammar::from_sentences(&[
        production(
            "Start",
            vec![ProductionItem::regex("[a-z]+")],
            Some("word"),
            precedence("1"),
        ),
        production(
            "Start",
            vec![ProductionItem::regex("[a-z]{2}")],
            Some("pair"),
            precedence("2"),
        ),
    ])
    .unwrap();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "ab");
}

#[test]
fn scanner_prefers_match_length_over_precedence() {
    let grammar = Grammar::from_sentences(&[
        production(
            "Start",
            vec![ProductionItem::regex("[a-z]{2}")],
            Some("highPrecedence"),
            precedence("99"),
        ),
        production(
            "Start",
            vec![ProductionItem::regex("[a-z]{3}")],
            Some("longer"),
            precedence("0"),
        ),
    ])
    .unwrap();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "abc");
}

#[test]
fn scanner_uses_the_longest_regex_alternative() {
    let grammar = Grammar::from_sentences(&[production(
        "Start",
        vec![ProductionItem::regex("a|ab")],
        Some("longestAlternative"),
        Attributes::default(),
    )])
    .unwrap();
    assert_inner_parse_snapshot!(grammar, Sort::new("Start"), "ab");
}

#[test]
fn rejects_inconsistent_scanner_precedence() {
    let sentences = vec![
        production(
            "First",
            vec![ProductionItem::regex("[a-z]+")],
            Some("first"),
            precedence("1"),
        ),
        production(
            "Second",
            vec![ProductionItem::regex("[a-z]+")],
            Some("second"),
            precedence("2"),
        ),
    ];

    assert!(matches!(
        Grammar::from_sentences(&sentences),
        Err(ParseError::InconsistentTokenPrecedence { .. })
    ));
}

#[test]
fn equivalent_k_regex_asts_share_a_scanner_lexeme() {
    let sentences = vec![
        production(
            "First",
            vec![ProductionItem::regex("(a)b")],
            Some("first"),
            precedence("1"),
        ),
        production(
            "Second",
            vec![ProductionItem::regex("ab")],
            Some("second"),
            precedence("2"),
        ),
    ];

    assert!(matches!(
        Grammar::from_sentences(&sentences),
        Err(ParseError::InconsistentTokenPrecedence { .. })
    ));
}

#[test]
fn reports_productive_unary_cycles_without_a_derivation_limit() {
    let sentences = vec![
        production(
            "Start",
            vec![ProductionItem::Terminal("x".into())],
            Some("base"),
            Attributes::default(),
        ),
        production(
            "Start",
            vec![nonterminal("Start")],
            Some("wrap"),
            Attributes::default(),
        ),
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    let error = grammar
        .parse(&Sort::new("Start"), "x")
        .expect_err("a productive unary cycle has an infinite parse forest");

    assert_eq!(error, ParseError::CyclicParseForest);
}

#[test]
fn rejects_non_associative_nesting() {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    let sentences = vec![
        production(
            "Id",
            vec![ProductionItem::regex("[a-z]")],
            None,
            token_attributes,
        ),
        production("Exp", vec![nonterminal("Id")], None, Attributes::default()),
        production(
            "Exp",
            vec![
                nonterminal("Exp"),
                ProductionItem::Terminal("<".into()),
                nonterminal("Exp"),
            ],
            Some("lessThan"),
            Attributes::default(),
        ),
        Sentence::SyntaxAssociativity {
            associativity: Associativity::NonAssoc,
            tags: vec!["lessThan".into()],
            attributes: Attributes::default(),
        },
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    assert_inner_parse_snapshot!(grammar, Sort::new("Exp"), "a < b < c");
}

#[test]
fn apply_priority_checks_only_selected_arguments() {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    let mut apply_priority = Attributes::default();
    apply_priority.insert("applyPriority", serde_json::json!("2"));
    let sentences = vec![
        production(
            "Exp",
            vec![ProductionItem::regex("[a-z]")],
            None,
            token_attributes,
        ),
        production(
            "Exp",
            vec![
                nonterminal("Exp"),
                ProductionItem::Terminal("+".into()),
                nonterminal("Exp"),
            ],
            Some("plus"),
            Attributes::default(),
        ),
        production(
            "Exp",
            vec![
                ProductionItem::Terminal("f(".into()),
                nonterminal("Exp"),
                ProductionItem::Terminal(",".into()),
                nonterminal("Exp"),
                ProductionItem::Terminal(",".into()),
                nonterminal("Exp"),
                ProductionItem::Terminal(")".into()),
            ],
            Some("f"),
            apply_priority,
        ),
        Sentence::SyntaxPriority {
            priorities: vec![vec!["f".into()], vec!["plus".into()]],
            attributes: Attributes::default(),
        },
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    assert!(
        grammar
            .parse(&Sort::new("Exp"), "f(a + b, c, a + b)")
            .is_ok()
    );
    assert_inner_parse_snapshot!(grammar, Sort::new("Exp"), "f(a, b + c, a)");
}

#[test]
fn filters_associativity_before_the_forest_limit() {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    let sentences = vec![
        production(
            "Exp",
            vec![ProductionItem::regex("[a-z]")],
            None,
            token_attributes,
        ),
        production(
            "Exp",
            vec![
                nonterminal("Exp"),
                ProductionItem::Terminal("+".into()),
                nonterminal("Exp"),
            ],
            Some("plus"),
            Attributes::default(),
        ),
        Sentence::SyntaxAssociativity {
            associativity: Associativity::Left,
            tags: vec!["plus".into()],
            attributes: Attributes::default(),
        },
    ];
    let grammar = Grammar::from_sentences(&sentences).unwrap();

    assert!(
        grammar
            .parse(
                &Sort::new("Exp"),
                "a + b + c + d + e + f + g + h + i + j + k + l",
            )
            .is_ok()
    );
}
