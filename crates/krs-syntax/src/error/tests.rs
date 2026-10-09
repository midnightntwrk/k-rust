use std::collections::HashSet;

use krs_diagnostic::Severity;

use super::*;

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One literal list of every syntax error category."
)]
fn syntax_categories_have_distinct_registered_codes() {
    let example = || String::from("example");
    let kinds = [
        SyntaxErrorKind::ReservedBinder,
        SyntaxErrorKind::RustSyntax(String::from("example")),
        SyntaxErrorKind::UnexpectedAttributePayload {
            attribute: "example",
        },
        SyntaxErrorKind::UnknownArgument {
            name: String::from("example"),
        },
        SyntaxErrorKind::DuplicateArgument { name: "example" },
        SyntaxErrorKind::MissingArgument { name: "example" },
        SyntaxErrorKind::InvalidArgumentValue {
            name: "example",
            expected: "example",
        },
        SyntaxErrorKind::UnsupportedPath,
        SyntaxErrorKind::UnsupportedSortDeclaration { reason: "example" },
        SyntaxErrorKind::UnsupportedConstructorDeclaration { reason: "example" },
        SyntaxErrorKind::UnsupportedEnumConstructorDeclaration { reason: "example" },
        SyntaxErrorKind::UnsupportedTokenDeclaration { reason: "example" },
        SyntaxErrorKind::UnsupportedSubsortDeclaration { reason: "example" },
        SyntaxErrorKind::InvalidSyntaxTemplate { reason: "example" },
        SyntaxErrorKind::UnknownTemplateField {
            name: String::from("example"),
        },
        SyntaxErrorKind::InvalidTemplateFieldOccurrence {
            name: String::from("example"),
            expected: 1,
            actual: 1,
        },
        SyntaxErrorKind::InvalidTokenRegex { reason: "example" },
        SyntaxErrorKind::InvalidFormat { reason: "example" },
        SyntaxErrorKind::InvalidStrictness { reason: "example" },
        SyntaxErrorKind::InvalidGrammarMacro { reason: "example" },
        SyntaxErrorKind::InvalidEnumPrecedence { reason: example() },
        SyntaxErrorKind::UnsupportedConfigurationDeclaration { reason: "example" },
        SyntaxErrorKind::UnsupportedConfigurationField { reason: "example" },
        SyntaxErrorKind::UnsupportedInitializerSignature { reason: "example" },
        SyntaxErrorKind::UnsupportedConfigurationVariable { reason: "example" },
        SyntaxErrorKind::AmbiguousMainConfigurationVariable,
        SyntaxErrorKind::UnsupportedInitializerBody { reason: "example" },
        SyntaxErrorKind::MissingConfigurationField { name: "example" },
        SyntaxErrorKind::DuplicateConfigurationField { name: "example" },
        SyntaxErrorKind::InvalidCellAttribute { reason: "example" },
        SyntaxErrorKind::InvalidStateMacro {
            macro_name: "example",
            reason: "example",
        },
        SyntaxErrorKind::InvalidTrivia { reason: "example" },
        SyntaxErrorKind::UnsupportedDslBlockComment {
            macro_name: "example",
        },
        SyntaxErrorKind::UnsupportedRuleSignature { reason: "example" },
        SyntaxErrorKind::UnsupportedRulePattern { reason: "example" },
        SyntaxErrorKind::InvalidTermType,
        SyntaxErrorKind::UnsupportedRuleBody { reason: "example" },
        SyntaxErrorKind::UnexpectedMacro {
            path: String::from("example"),
        },
        SyntaxErrorKind::UnsupportedTermExpression { reason: "example" },
        SyntaxErrorKind::MissingTokenEndpoint,
        SyntaxErrorKind::TooManyProvenanceOccurrences { role: "example" },
        SyntaxErrorKind::InvalidColor { reason: "example" },
        SyntaxErrorKind::InvalidRuleKey { reason: "example" },
        SyntaxErrorKind::RetiredAttribute {
            attribute: "example",
            replacement: String::from("example"),
        },
        SyntaxErrorKind::InvalidTokenAttribute { reason: "example" },
        SyntaxErrorKind::InvalidLexicalMacro { reason: "example" },
        SyntaxErrorKind::InvalidSyntaxList { reason: "example" },
        SyntaxErrorKind::RawKShape { reason: example() },
        SyntaxErrorKind::InvalidSmtMetadata { reason: example() },
        SyntaxErrorKind::InvalidMatchRestriction { reason: example() },
        SyntaxErrorKind::InvalidUnboundVariables { reason: example() },
        SyntaxErrorKind::InvalidSpecModule { reason: example() },
        SyntaxErrorKind::InvalidPatternAs {
            reason: String::from("example"),
        },
        SyntaxErrorKind::InvalidPatternOr {
            reason: String::from("example"),
        },
        SyntaxErrorKind::InvalidMatches {
            reason: String::from("example"),
        },
    ];
    let mut seen = HashSet::new();
    for kind in kinds {
        let code = kind.code();
        assert!(codes::REGISTRY.iter().any(|info| info.code == code));
        assert!(seen.insert(code), "duplicate code for {kind:?}");
    }
    assert_eq!(
        seen.len(),
        codes::REGISTRY
            .iter()
            .filter(|info| info.code.as_str().starts_with("krs::syntax::"))
            .count()
    );
}

#[test]
fn diagnostic_preserves_the_span_and_display_text_without_a_source_range() {
    let tokens: proc_macro2::TokenStream = "  unsupported".parse().unwrap();
    let span = tokens.into_iter().next().unwrap().span();
    let error = SyntaxError::new(SyntaxErrorKind::UnsupportedPath, span);
    let diagnostic = error.to_diagnostic();
    assert_eq!(diagnostic.code, codes::syntax::UNSUPPORTED_PATH);
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(diagnostic.message, error.to_string());
    let Location::Span(actual) = diagnostic.primary.location else {
        panic!("expected the producer span");
    };
    assert_eq!(actual.byte_range(), span.byte_range());
    let rust_error = syn::Error::from(error);
    assert_eq!(rust_error.to_string(), diagnostic.message);
    assert_eq!(rust_error.span().byte_range(), span.byte_range());
}

#[test]
fn diagnostic_prefers_the_exact_trivia_range_and_keeps_the_rust_span() {
    let source = "é /* comment */ token";
    let tokens: proc_macro2::TokenStream = source.parse().unwrap();
    let span = tokens.into_iter().last().unwrap().span();
    let range = SourceRange::new(3, 16).unwrap();
    let error = SyntaxError::new(
        SyntaxErrorKind::UnsupportedDslBlockComment {
            macro_name: "rules",
        },
        span,
    )
    .with_source_range(range);
    let diagnostic = error.to_diagnostic();
    assert_eq!(
        diagnostic.code,
        codes::syntax::UNSUPPORTED_DSL_BLOCK_COMMENT
    );
    assert_eq!(diagnostic.message, error.to_string());
    let Location::Range(actual) = diagnostic.primary.location else {
        panic!("expected the exact input range");
    };
    assert_eq!(actual, range);
    assert_eq!(&source[actual.start()..actual.end()], "/* comment */");
    let rust_error = syn::Error::from(error);
    assert_eq!(rust_error.to_string(), diagnostic.message);
    assert_eq!(rust_error.span().byte_range(), span.byte_range());
}
