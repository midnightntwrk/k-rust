use k_rust::definition::{Associativity, Attributes, ProductionItem, Sentence};
use k_rust::inner::{Grammar, ParseError};
use k_rust::kast::{Label, Sort, Term};

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

#[test]
fn matches_scala_module_defined_layout_selection() {
    let start = production(
        "Start",
        vec![ProductionItem::Terminal("x".into())],
        Some("x"),
        Attributes::default(),
    );
    let default = Grammar::from_sentences([&start]).unwrap();

    let custom_sentences = [
        start.clone(),
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
    ];
    let custom = Grammar::from_sentences(&custom_sentences).unwrap();

    let disabled_sentences = [start.clone(), syntax_sort("#Layout")];
    let disabled = Grammar::from_sentences(&disabled_sentences).unwrap();

    let results = [
        default.parse(&Sort::new("Start"), " /* default */ x // tail"),
        custom.parse(&Sort::new("Start"), "~~ _ x~~~"),
        custom.parse(&Sort::new("Start"), "/* not custom */ x"),
        disabled.parse(&Sort::new("Start"), "x"),
        disabled.parse(&Sort::new("Start"), " x"),
    ];

    insta::assert_debug_snapshot!(results);
}

#[test]
fn rejects_invalid_or_empty_layout_productions() {
    let invalid = [
        syntax_sort("#Layout"),
        production(
            "#Layout",
            vec![ProductionItem::Terminal(" ".into())],
            None,
            Attributes::default(),
        ),
    ];
    let empty = [
        syntax_sort("#Layout"),
        production(
            "#Layout",
            vec![ProductionItem::regex("a*")],
            None,
            Attributes::default(),
        ),
    ];

    insta::assert_debug_snapshot!([
        Grammar::from_sentences(&invalid).unwrap_err(),
        Grammar::from_sentences(&empty).unwrap_err(),
    ]);
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

    assert_eq!(
        grammar.parse(&Sort::new("Start"), "x"),
        Err(ParseError::Ambiguous { parses: 2 })
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
fn matches_scala_global_scanner_winner_rules() {
    let cases = [
        (
            vec![
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
            ],
            "==",
        ),
        (
            vec![
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
            ],
            "if",
        ),
        (
            vec![
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
            ],
            "ab",
        ),
        (
            vec![
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
            ],
            "abc",
        ),
        (
            vec![production(
                "Start",
                vec![ProductionItem::regex("a|ab")],
                Some("longestAlternative"),
                Attributes::default(),
            )],
            "ab",
        ),
    ];
    let parsed = cases
        .into_iter()
        .map(|(sentences, input)| {
            Grammar::from_sentences(&sentences)
                .unwrap()
                .parse(&Sort::new("Start"), input)
        })
        .collect::<Vec<_>>();

    insta::assert_debug_snapshot!(parsed);
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
fn bounds_cyclic_parse_forests() {
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

    assert_eq!(
        grammar.parse(&Sort::new("Start"), "x"),
        Err(ParseError::TooManyParses { limit: 64 })
    );
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

    insta::assert_debug_snapshot!(grammar.parse(&Sort::new("Exp"), "a < b < c"));
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
    insta::assert_debug_snapshot!(grammar.parse(&Sort::new("Exp"), "f(a, b + c, a)"));
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
