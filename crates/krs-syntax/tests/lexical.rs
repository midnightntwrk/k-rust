//! `k::lexical!` and `k::layout!` payloads and `{Name}` references (KF-004).

use krs_syntax::{
    KrsSyntax, LayoutDeclaration, LexicalDeclaration, ProvenanceRole, SyntaxErrorKind,
    regex_references,
};

fn reason(error: &krs_syntax::SyntaxError) -> &'static str {
    match error.kind() {
        SyntaxErrorKind::InvalidLexicalMacro { reason }
        | SyntaxErrorKind::InvalidTokenRegex { reason } => reason,
        other => panic!("unexpected error kind {other:?}"),
    }
}

#[test]
fn lexical_entries_keep_names_regexes_docs_and_anchors() {
    let declaration = LexicalDeclaration::parse_source(
        r#"
        /// One ASCII letter.
        Alpha = r"[a-zA-Z]";
        AlphaNum = r"[a-zA-Z0-9_]";
        "#,
    )
    .unwrap();
    let entries = declaration.entries();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].name(), "Alpha");
    assert_eq!(entries[0].regex().value(), "[a-zA-Z]");
    assert_eq!(entries[0].attributes().len(), 1);
    assert_eq!(entries[1].name(), "AlphaNum");
    let roles = declaration
        .provenance()
        .unwrap()
        .iter()
        .map(|anchor| (anchor.key().role(), anchor.key().ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            (ProvenanceRole::LexicalDeclaration, 0),
            (ProvenanceRole::LexicalRegex, 0),
            (ProvenanceRole::LexicalDeclaration, 1),
            (ProvenanceRole::LexicalRegex, 1),
        ]
    );
}

#[test]
fn malformed_lexical_blocks_are_rejected() {
    for (source, expected) in [
        ("", "`k::lexical!` must declare at least one"),
        (
            r#"alpha = r"[a-z]";"#,
            "a lexical name matches `[A-Z][A-Za-z0-9]*`",
        ),
        (
            r#"Alpha_1 = r"[a-z]";"#,
            "a lexical name matches `[A-Z][A-Za-z0-9]*`",
        ),
        (
            r#"Alpha = r"[a-z]"; Alpha = r"[A-Z]";"#,
            "a lexical name is declared once",
        ),
        (r#"Alpha = "";"#, "the regex must not be empty"),
        (r#"Alpha = r"[a-z";"#, "unclosed character class"),
        (
            r#"#[allow(dead_code)] Alpha = r"[a-z]";"#,
            "a `k::lexical!` entry takes only doc comments",
        ),
    ] {
        let error = LexicalDeclaration::parse_source(source).unwrap_err();
        assert!(reason(&error).starts_with(expected), "{source}: {error}");
    }
    assert!(LexicalDeclaration::parse_source(r#"Alpha = r"[a-z]""#).is_err());
}

#[test]
fn layout_blocks_take_nonempty_well_formed_regexes() {
    let declaration =
        LayoutDeclaration::parse_source(r#"r"(;[^\n\r]*)", r"([\ \n\r\t])","#).unwrap();
    assert_eq!(declaration.regexes().len(), 2);
    let roles = declaration
        .provenance()
        .unwrap()
        .iter()
        .map(|anchor| (anchor.key().role(), anchor.key().ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            (ProvenanceRole::LayoutRegex, 0),
            (ProvenanceRole::LayoutRegex, 1)
        ]
    );
    for (source, expected) in [
        ("", "`k::layout!` must declare at least one regex"),
        (r#"r"""#, "the regex must not be empty"),
        (r#"r"(a""#, "unclosed parenthesis"),
    ] {
        let error = LayoutDeclaration::parse_source(source).unwrap_err();
        assert!(reason(&error).starts_with(expected), "{source}: {error}");
    }
}

#[test]
fn references_are_named_braces_outside_classes_and_escapes() {
    assert_eq!(
        regex_references(r"{Alpha}{AlphaNum}*"),
        ["Alpha", "AlphaNum"]
    );
    assert_eq!(
        regex_references(r"[{]\{Not\}a{2}b{1,3}"),
        Vec::<String>::new()
    );
    assert_eq!(regex_references(r"{Alpha}|{Alpha}{}"), ["Alpha", ""]);
}
