//! Fields of production declarations take doc comments and no other
//! attribute: a doc comment documents the Rust item and has no K meaning.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    ConstructorDeclaration, EnumConstructorDeclaration, SyntaxError, SyntaxListAttribute,
    SyntaxListDeclaration, TokenDeclaration,
};

/// The doc attribute forms rustc accepts on a field.
const DOCS: [&str; 3] = [
    "/// The field.\n",
    "#[doc = \"The field.\"]",
    "#[doc(hidden)]",
];

fn constructor(attribute: &str) -> Result<ConstructorDeclaration, SyntaxError> {
    ConstructorDeclaration::parse_source(&format!(
        "pub struct Byte {{ {attribute} pub value: k::Term<Int> }}"
    ))
}

fn enum_constructor(attribute: &str) -> Result<EnumConstructorDeclaration, SyntaxError> {
    EnumConstructorDeclaration::parse_source(&format!(
        "#[k::constructors(sort = Stmt, result = KResult)] \
         pub enum Extra {{ #[k::syntax(\"tag({{n}})\")] Tag {{ {attribute} n: Int }} }}"
    ))
}

fn syntax_list(attribute: &str) -> Result<SyntaxListDeclaration, SyntaxError> {
    SyntaxListDeclaration::from_parts(
        &SyntaxListAttribute::parse_source(r#"separator = ",""#).unwrap(),
        syn::parse_str(&format!(
            "pub enum Ints {{ Cons {{ head: Int, {attribute} tail: Ints }}, Nil() }}"
        ))
        .unwrap(),
    )
}

fn token(attribute: &str) -> Result<TokenDeclaration, SyntaxError> {
    TokenDeclaration::parse_source(&format!("pub struct Name({attribute} pub String);"))
}

/// Asserts that `result` is an error with `message` at the refused
/// attribute, which starts the source's second line.
fn assert_refused<T>(result: Result<T, SyntaxError>, attribute: &str, message: &str) {
    let Err(error) = result else {
        panic!("{attribute} was accepted");
    };
    assert!(error.to_string().ends_with(message), "{attribute}: {error}");
    let start = error.span().start();
    assert_eq!((start.line, start.column), (2, 0), "{attribute}: {error}");
}

#[test]
fn production_fields_accept_doc_comments() {
    for doc in DOCS {
        let declaration = constructor(doc).unwrap();
        assert_eq!(declaration.fields().len(), 1, "{doc}");
        let family = enum_constructor(doc).unwrap();
        assert_eq!(family.variants()[0].fields().len(), 1, "{doc}");
        let list = syntax_list(doc).unwrap();
        assert_eq!(list.cons().tail().name(), "tail", "{doc}");
        token(doc).unwrap();
    }
}

#[test]
fn production_fields_refuse_other_attributes_at_the_attribute() {
    for attribute in ["#[allow(clippy::pedantic)]", "#[cfg(any())]"] {
        // A doc comment before the refused attribute does not hide it.
        let attributes = format!("/// The field.\n{attribute}");
        assert_refused(
            constructor(&attributes),
            attribute,
            "a constructor field takes only doc comments",
        );
        assert_refused(
            enum_constructor(&attributes),
            attribute,
            "an enum constructor field takes only doc comments",
        );
        assert_refused(
            syntax_list(&attributes),
            attribute,
            "a syntactic-list field takes only doc comments",
        );
        assert_refused(
            token(&attributes),
            attribute,
            "the token representation field takes only doc comments",
        );
    }
}
