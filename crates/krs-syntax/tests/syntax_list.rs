//! `#[k::syntax_list]` attributes and enums (KF-020).

use krs_syntax::{
    KrsSyntax, ProvenanceRole, StrictnessKind, SyntaxErrorKind, SyntaxListAttribute,
    SyntaxListDeclaration,
};

fn declaration(attribute: &str, item: &str) -> Result<SyntaxListDeclaration, String> {
    let attribute = SyntaxListAttribute::parse_source(attribute).map_err(|error| reason(&error))?;
    SyntaxListDeclaration::from_parts(&attribute, syn::parse_str(item).unwrap())
        .map_err(|error| reason(&error))
}

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidSyntaxList { reason } => (*reason).to_owned(),
        other => format!("{other:?}"),
    }
}

const INTS: &str = "pub enum Ints { Cons { head: Int, tail: Ints }, Nil() }";

#[test]
fn readable_list_keeps_separator_variants_and_anchors() {
    let list = declaration(r#"separator = ",""#, INTS).unwrap();
    assert_eq!(list.name(), "Ints");
    assert_eq!(list.attribute().separator().value(), ",");
    assert!(list.attribute().non_empty().is_none());
    assert!(!list.attribute().is_reference());
    assert_eq!(list.cons().name(), "Cons");
    assert_eq!(list.cons().head().name(), "head");
    assert_eq!(list.cons().tail().name(), "tail");
    assert_eq!(list.terminator().name(), "Nil");
    let roles = |anchors: Vec<krs_syntax::ProvenanceAnchor>| {
        anchors
            .iter()
            .map(krs_syntax::ProvenanceAnchor::role)
            .collect::<Vec<_>>()
    };
    let cons = roles(list.cons_provenance().unwrap());
    assert!(cons.contains(&ProvenanceRole::ListDeclaration));
    assert!(cons.contains(&ProvenanceRole::ListSeparator));
    assert!(!cons.contains(&ProvenanceRole::ListNonEmpty));
    let terminator = roles(list.terminator_provenance().unwrap());
    assert!(terminator.contains(&ProvenanceRole::ListDeclaration));
    assert!(!terminator.contains(&ProvenanceRole::ListSeparator));
}

#[test]
fn variant_order_is_free_and_separator_may_be_empty() {
    let list = declaration(
        r#"separator = "", non_empty"#,
        "pub enum Ops { Nil(), More { first: Int, rest: Ops } }",
    )
    .unwrap();
    assert_eq!(list.cons().name(), "More");
    assert_eq!(list.terminator().name(), "Nil");
    assert!(list.attribute().non_empty().is_some());
    assert!(
        list.cons_provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::ListNonEmpty)
    );
}

#[test]
fn readable_strictness_inherits_the_list_result() {
    let list = declaration(
        r#"separator = ",", result = KResult"#,
        "pub enum Args { #[k::strict] Cons { head: Expr, tail: Args }, Nil() }",
    )
    .unwrap();
    let strictness = list.cons().strictness().unwrap();
    assert_eq!(strictness.kind(), StrictnessKind::Strict);
    assert_eq!(strictness.fields().len(), 2);
    assert!(strictness.result_sort().is_ident("KResult"));
}

#[test]
fn reference_list_writes_term_fields_and_the_result_on_strictness() {
    let list = declaration(
        r#"separator = ",", reference"#,
        "pub enum Args { #[k::strict(sequence = [head, tail], result = k::KResult)] \
         Cons { head: k::Term<dyn crate::ExprSort>, tail: k::Term<crate::Args> }, Nil() }",
    )
    .unwrap();
    assert!(list.attribute().is_reference());
    assert!(list.cons().head().term_sort().is_dynamic());
    assert!(list.cons().strictness().is_some());
}

#[test]
fn malformed_lists_are_rejected() {
    let cases = [
        (
            r#"separator = ",""#,
            "pub enum Ints { Cons { head: Int, tail: Ints }, Nil(), Empty() }",
            "exactly two variants",
        ),
        (
            r#"separator = ",""#,
            "pub enum Ints { Cons { head: Int, tail: Int }, Nil() }",
            "the second field of the cons variant is the list itself",
        ),
        (
            r#"separator = ",""#,
            "pub enum Ints { Cons { head: Int, tail: Ints }, Nil }",
            "zero-field tuple terminator",
        ),
        (
            r#"separator = ",""#,
            "pub enum Ints { Cons { head: Int }, Nil() }",
            "zero-field tuple terminator",
        ),
        (
            r#"separator = ",""#,
            "pub enum Ints<T> { Cons { head: Int, tail: Ints<T> }, Nil() }",
            "generic parameters",
        ),
        (
            r#"separator = ",""#,
            r#"pub enum Ints { #[k::syntax("{head}")] Cons { head: Int, tail: Ints }, Nil() }"#,
            "take no `#[k::syntax]`",
        ),
        (
            r#"separator = ",""#,
            "pub enum Ints { Cons { head: Int, tail: Ints }, #[k::strict] Nil() }",
            "the terminator variant has no fields",
        ),
        (
            r#"separator = ",""#,
            "pub enum Ints { #[k::strict] Cons { head: Int, tail: Ints }, Nil() }",
            "inherits its result sort",
        ),
        (
            r#"separator = ",", result = KResult"#,
            INTS,
            "add the strictness or drop `result`",
        ),
        (r#"separator = "a+""#, INTS, "exactly one K terminal"),
        (r#"separator = ", ""#, INTS, "exactly one K terminal"),
        (
            r#"separator = ",", non_empty, non_empty"#,
            INTS,
            "written once",
        ),
        ("non_empty", INTS, "requires `separator"),
        (
            r#"separator = ",", result = KResult, reference"#,
            INTS,
            "on the cons variant's strictness attribute",
        ),
    ];
    for (attribute, item, expected) in cases {
        let error = declaration(attribute, item).unwrap_err();
        assert!(
            error.contains(expected),
            "{attribute} / {item}: {error:?} lacks {expected:?}"
        );
    }
}
