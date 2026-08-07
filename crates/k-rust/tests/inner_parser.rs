use k_rust::definition::{Attributes, ProductionItem, Sentence};
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
