//! Sort-parametric productions (KF-027): `struct Choose<S: ?Sized>` declares
//! K's `syntax {S}`, and a turbofish on a term head names an instance.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    ConstructorDeclaration, ProvenanceRole, RuleItem, SyntaxErrorKind, TermExpression, TermTree,
};

const CHOOSE: &str = "pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}";

#[test]
fn a_sort_parameter_is_a_question_sized_type_parameter_named_by_fields() {
    let declaration = ConstructorDeclaration::parse_source(CHOOSE).unwrap();
    let parameters = declaration
        .sort_parameters()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert_eq!(parameters, ["S"]);
    let fields = declaration
        .fields()
        .iter()
        .map(|field| (field.name().to_string(), field.parameter()))
        .collect::<Vec<_>>();
    assert_eq!(
        fields,
        [
            ("cond".to_owned(), None),
            ("then_branch".to_owned(), Some(0)),
            ("else_branch".to_owned(), Some(0)),
        ]
    );
    assert_eq!(
        declaration.sort_parameter_index(&syn::parse_quote!(S)),
        Some(0)
    );
    assert_eq!(
        declaration.sort_parameter_index(&syn::parse_quote!(crate::S)),
        None
    );
    let anchors = declaration.provenance().unwrap();
    let parameter = anchors
        .iter()
        .find(|anchor| anchor.role() == ProvenanceRole::SortParameter)
        .expect("the parameter has an anchor");
    assert_eq!(parameter.ordinal(), 0);
}

#[test]
fn generics_other_than_sort_parameters_are_rejected() {
    for (source, reason) in [
        (
            "struct F<'a, S: ?Sized> { value: Term<S> }",
            "lifetime parameters",
        ),
        (
            "struct F<S: ?Sized, const W: usize> { value: Term<S> }",
            "machine-integer widths (KF-034)",
        ),
        ("struct F<S> { value: Term<S> }", "write `S: ?Sized`"),
        (
            "struct F<S: ?Sized + Expr> { value: Term<S> }",
            "write `S: ?Sized`",
        ),
        (
            "struct F<S: ?Sized = Int> { value: Term<S> }",
            "cannot have a default",
        ),
        (
            "struct F<S: ?Sized> where S: 'static { value: Term<S> }",
            "where clause",
        ),
        (
            "struct F<S: ?Sized, T: ?Sized> { value: Term<S> }",
            "sort parameter `T` is used by no field",
        ),
    ] {
        let error = ConstructorDeclaration::parse_source(source).unwrap_err();
        let SyntaxErrorKind::InvalidSortParameter { reason: actual } = error.kind() else {
            panic!("{source}: {:?}", error.kind());
        };
        assert!(actual.contains(reason), "{source}: {actual}");
    }
}

#[test]
fn a_turbofish_names_the_instance_and_leaves_the_head_plain() {
    for (source, markers) in [
        (
            "Choose::<k::builtin::Int> { cond: true, then_branch: a, else_branch: b }",
            vec![(false, "k :: builtin :: Int")],
        ),
        ("Choose::<dyn ExpSort>(c, a, b)", vec![(true, "ExpSort")]),
        (
            "Pair::<Int, dyn ExpSort>(a, b)",
            vec![(false, "Int"), (true, "ExpSort")],
        ),
    ] {
        let term = TermExpression::parse_source(source).unwrap();
        let TermTree::Application(application) = term.tree() else {
            panic!("{source} is an application");
        };
        assert!(
            application
                .head()
                .segments
                .iter()
                .all(|segment| segment.arguments.is_none()),
            "{source}"
        );
        let actual = application
            .instance()
            .iter()
            .map(|sort| (sort.is_dynamic(), sort.sort_token_text()))
            .collect::<Vec<_>>();
        let expected = markers
            .into_iter()
            .map(|(dynamic, text)| (dynamic, text.to_owned()))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source}");
    }
}

#[test]
fn a_turbofish_lists_sort_markers_on_the_last_segment_only() {
    for source in [
        "Choose::<'static>(c, a, b)",
        "Choose::<3>(c, a, b)",
        "Choose::<>(c, a, b)",
        "module::<Int>::Choose(c, a, b)",
        "Choose::<&Int>(c, a, b)",
    ] {
        let error = TermExpression::parse_source(source).unwrap_err();
        assert!(
            matches!(
                error.kind(),
                SyntaxErrorKind::InvalidTurbofish { .. } | SyntaxErrorKind::UnsupportedPath
            ),
            "{source}: {:?}",
            error.kind()
        );
    }
}

#[test]
fn turbofish_markers_are_anchored_once_across_a_sentence() {
    let rule = RuleItem::parse_equation_source(
        "fn choose_true(
            k::term![Choose::<Int> { cond: true, then_branch: a, else_branch: _ }]: Term<Int>,
        ) -> Term<Int> {
            Choose::<Int> { cond: false, then_branch: a, else_branch: a }
        }",
    )
    .unwrap();
    let anchors = rule.full_provenance().unwrap();
    let ordinals = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ApplicationInstance)
        .map(krs_syntax::ProvenanceAnchor::ordinal)
        .collect::<Vec<_>>();
    assert_eq!(ordinals, [0, 1]);
}

#[test]
fn rules_never_quantify_over_sorts() {
    let error = RuleItem::parse_equation_source(
        "fn choose_true<S: ?Sized>(
            k::term![Choose::<S> { cond: true, then_branch: a, else_branch: _ }]: Term<S>,
        ) -> Term<S> {
            a
        }",
    )
    .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("K rules never quantify over sorts"),
        "{error}"
    );
}
