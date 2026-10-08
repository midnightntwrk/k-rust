//! User token sorts: stacked `#[k::token]` attributes, alias carriers, and
//! `k::lexeme!` terms (KF-003).

use krs_syntax::{
    KrsSyntax, ProvenanceRole, SyntaxErrorKind, TermExpression, TermNode, TermTree, TokenAttribute,
    TokenCarrier, TokenContent, TokenDeclaration, TokenStack,
};

fn reason(error: &krs_syntax::SyntaxError) -> &'static str {
    match error.kind() {
        SyntaxErrorKind::InvalidTokenAttribute { reason }
        | SyntaxErrorKind::InvalidTokenRegex { reason } => reason,
        other => panic!("unexpected error kind {other:?}"),
    }
}

#[test]
fn a_token_attribute_takes_one_regex_or_one_terminal() {
    let regex = TokenAttribute::parse_source(r#"regex = r"[a-z]+", prec = 2"#).unwrap();
    assert!(matches!(regex.content(), TokenContent::Regex(_)));
    assert_eq!(regex.lexical_precedence(), Some(2));
    let terminal = TokenAttribute::parse_source(r#"terminal = "main""#).unwrap();
    assert_eq!(terminal.terminal().unwrap().value(), "main");
    assert!(terminal.regex().is_none());

    for (source, expected) in [
        ("prec = 1", "a token attribute takes exactly one of"),
        (
            r#"regex = r"[a-z]+", terminal = "main""#,
            "stack one `#[k::token]` attribute",
        ),
        (
            r#"terminal = "main", regex = r"[a-z]+""#,
            "stack one `#[k::token]` attribute",
        ),
        (
            r#"terminal = "main", prec = 1"#,
            "`prec` orders regex tokens only",
        ),
        (r#"terminal = """#, "the token terminal must not be empty"),
        (r#"terminal = "a b""#, "exactly one K terminal"),
        (r#"terminal = "a+""#, "exactly one K terminal"),
        ("regex = r#\"\"[a-z]*\"\"#", "a literal quote is written"),
    ] {
        let error = TokenAttribute::parse_source(source).unwrap_err();
        assert!(reason(&error).contains(expected), "{source}: {error}");
    }
    assert!(matches!(
        TokenAttribute::parse_source(r#"terminal = "a", terminal = "b""#)
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::DuplicateArgument { name: "terminal" }
    ));
    // An escaped quote is a literal quote.
    TokenAttribute::parse_source("regex = r#\"\\\"[a-z]*\\\"\"#").unwrap();
    // A terminal of symbol characters, or of word characters, is one K terminal.
    TokenAttribute::parse_source(r#"terminal = "+=""#).unwrap();
}

#[test]
fn stacked_attributes_number_their_anchors_per_kind() {
    let stack = TokenStack::new(vec![
        TokenAttribute::parse_source(r#"regex = r"[a-z]+", prec = 1"#).unwrap(),
        TokenAttribute::parse_source(r#"terminal = "main""#).unwrap(),
        TokenAttribute::parse_source(r#"regex = r"\$[a-z]+""#).unwrap(),
    ])
    .unwrap();
    let keys = stack
        .provenance()
        .unwrap()
        .iter()
        .map(|anchor| (anchor.role(), anchor.key().ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            (ProvenanceRole::TokenRegex, 0),
            (ProvenanceRole::TokenLexicalPrecedence, 0),
            (ProvenanceRole::TokenTerminal, 0),
            (ProvenanceRole::TokenRegex, 1),
        ]
    );

    let duplicate = TokenStack::new(vec![
        TokenAttribute::parse_source(r#"terminal = "main""#).unwrap(),
        TokenAttribute::parse_source(r#"terminal = "main""#).unwrap(),
    ])
    .unwrap_err();
    assert!(reason(&duplicate).contains("repeats an earlier one"));
    // A regex and a terminal with the same text are different productions.
    TokenStack::new(vec![
        TokenAttribute::parse_source(r#"regex = r"main""#).unwrap(),
        TokenAttribute::parse_source(r#"terminal = "main""#).unwrap(),
    ])
    .unwrap();
}

#[test]
fn a_type_alias_carries_tokens_for_an_existing_sort() {
    let alias = TokenDeclaration::parse_source("pub type DollarId = k::builtin::Id;").unwrap();
    assert!(matches!(alias.carrier(), TokenCarrier::Alias(_)));
    assert_eq!(alias.name(), "DollarId");
    assert!(alias.item().is_none());
    assert_eq!(
        alias.provenance().unwrap()[0].role(),
        ProvenanceRole::TokenDeclaration
    );
    for source in [
        "type Alias<T> = Name<T>;",
        "type Alias = (Name, Name);",
        "type Alias = <Name as Trait>::Output;",
        "enum Name {}",
    ] {
        assert!(
            matches!(
                TokenDeclaration::parse_source(source).unwrap_err().kind(),
                SyntaxErrorKind::UnsupportedTokenDeclaration { .. }
            ),
            "{source}"
        );
    }
}

#[test]
fn a_lexeme_is_a_sort_path_and_a_nonempty_text() {
    let term = TermExpression::parse_source(r#"Call(k::lexeme!(Name, "main"))"#).unwrap();
    let TermTree::Application(application) = term.tree() else {
        panic!("expected an application");
    };
    let [TermTree::Lexeme { sort, text }] = application.arguments().positional().unwrap() else {
        panic!("expected one lexeme argument");
    };
    assert!(sort.is_ident("Name"));
    assert_eq!(text.value(), "main");
    assert!(
        term.nodes()
            .iter()
            .any(|node| matches!(node, TermNode::Lexeme { .. }))
    );
    // The sort path is not a reference to resolve as a constructor.
    assert!(
        term.symbols()
            .iter()
            .all(|symbol| !symbol.path().is_ident("Name"))
    );

    for (source, expected) in [
        (
            r"k::lexeme!(Name)",
            "takes exactly a token sort path and a string literal",
        ),
        (
            r#"k::lexeme!(Name, "a", "b")"#,
            "takes exactly a token sort path",
        ),
        (
            r#"k::lexeme!("main", Name)"#,
            "takes exactly a token sort path",
        ),
        (r#"k::lexeme!(Name, "")"#, "text must not be empty"),
    ] {
        let error = TermExpression::parse_source(source).unwrap_err();
        assert!(reason(&error).contains(expected), "{source}: {error}");
    }
}
