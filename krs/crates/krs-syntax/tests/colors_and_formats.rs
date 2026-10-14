//! Production colours, `%c`/`%r`, and terminal positions in formats (KF-018).

use krs_syntax::{
    KrsSyntax, ProvenanceRole, StructuredFormatFragment as Fragment, SyntaxErrorKind,
};

fn readable_variant(attribute: &str, helpers: &str) -> krs_syntax::EnumConstructorDeclaration {
    krs_syntax::EnumConstructorDeclaration::parse_source(&format!(
        r"#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Node))]
pub enum Family {{
    {attribute}
    {helpers}
    Node {{ condition: Expr, body: Stmt }},
}}"
    ))
    .unwrap()
}

#[test]
fn readable_formats_refer_to_terminals_by_position() {
    let declaration = readable_variant(
        r#"#[k::syntax("while ({condition}) {body}", color = "magenta")]"#,
        "",
    );
    let syntax = declaration.variants()[0].syntax().unwrap();
    assert_eq!(syntax.color().unwrap().value(), "magenta");
    assert_eq!(
        syntax.structured_format().unwrap().fragments(),
        [
            Fragment::Item(1),
            Fragment::Literal(" ".into()),
            Fragment::Item(2),
            Fragment::Item(3),
            Fragment::Item(4),
            Fragment::Literal(" ".into()),
            Fragment::Item(5),
        ]
    );
    let roles = declaration
        .variant_provenance(&declaration.variants()[0])
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::ConstructorColor));
}

#[test]
fn colors_count_terminals_and_color_controls() {
    let attribute = krs_syntax::VariantSyntaxAttribute::parse_source(
        r#""x = {value};", colors = ["green", "red", "red", "red"], format = "%c// assign%r%nx = {value};""#,
    )
    .unwrap();
    assert_eq!(
        attribute
            .colors()
            .unwrap()
            .iter()
            .map(syn::LitStr::value)
            .collect::<Vec<_>>(),
        ["green", "red", "red", "red"]
    );
    assert_eq!(attribute.structured_format().unwrap().color_next_count(), 1);
}

#[test]
fn block_format_numbers_both_braces() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Block))]
pub enum Family {
    #[k::syntax("{{{body}}}", colors = ["blue", "blue"])]
    #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },
}"#,
    )
    .unwrap();
    let syntax = declaration.variants()[0].syntax().unwrap();
    assert_eq!(
        syntax.structured_format().unwrap().fragments(),
        [
            Fragment::Item(1),
            Fragment::Indent,
            Fragment::Newline,
            Fragment::Item(2),
            Fragment::Dedent,
            Fragment::Newline,
            Fragment::Item(3),
        ]
    );
}

#[test]
fn assignment_comment_stays_literal() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((AssignX))]
pub enum Family {
    #[k::syntax("x = {value};", colors = ["green", "red", "red", "red"])]
    #[k::format("%c// assign%r%nx = {value};")]
    AssignX { value: Int },
}"#,
    )
    .unwrap();
    let syntax = declaration.variants()[0].syntax().unwrap();
    assert_eq!(
        syntax.structured_format().unwrap().fragments(),
        [
            Fragment::ColorNext,
            Fragment::Literal("// assign".into()),
            Fragment::ColorReset,
            Fragment::Newline,
            Fragment::Item(1),
            Fragment::Literal(" ".into()),
            Fragment::Item(2),
            Fragment::Literal(" ".into()),
            Fragment::Item(3),
            Fragment::Item(4),
        ]
    );
}

#[test]
fn reference_constructor_formats_number_terminals() {
    let attribute = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Expr, syntax = "{lhs} + {rhs}", color = "red", format = "%1 + %3""#,
    )
    .unwrap();
    assert_eq!(attribute.color().unwrap().value(), "red");
    assert_eq!(
        attribute.structured_format().unwrap().fragments(),
        [
            Fragment::Item(1),
            Fragment::Literal(" ".into()),
            Fragment::Item(2),
            Fragment::Literal(" ".into()),
            Fragment::Item(3),
        ]
    );
}

#[test]
fn color_diagnostics() {
    let invalid = |reason: &'static str| SyntaxErrorKind::InvalidColor { reason };
    let cases = [
        (
            r#""a {x}", color = "red", colors = ["red"]"#,
            invalid("`color` and `colors` cannot be combined"),
        ),
        (
            r#""a {x}", color = """#,
            invalid("a colour must be nonempty and must not contain `,` or `)`"),
        ),
        (
            r#""a {x}", color = "red,blue""#,
            invalid("a colour must be nonempty and must not contain `,` or `)`"),
        ),
        (
            r#""a {x}", colors = ["red)"]"#,
            invalid("a colour must be nonempty and must not contain `,` or `)`"),
        ),
        (
            r#""a {x} b", colors = ["red"], format = "a {x} b""#,
            invalid(
                "`colors` needs one colour per terminal of the syntax template plus one per `%c`",
            ),
        ),
        (
            r#""a {x}", format = "%ca%r {x}""#,
            invalid("`%c` and `%r` need a `color` or `colors` key"),
        ),
        (
            r#""a {x}", format = "%q""#,
            SyntaxErrorKind::InvalidFormat {
                reason: "`%` must be followed by `%n`, `%i`, `%d`, `%c`, `%r`, `%%`, or a one-based item position",
            },
        ),
    ];
    for (source, expected) in cases {
        let error = krs_syntax::VariantSyntaxAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
}
