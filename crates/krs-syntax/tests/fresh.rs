//! Fresh values (KF-022): the `#[k::fresh]` rule helper and the bare
//! `fresh_generator` flag of `#[k::function]`.

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

#[test]
fn function_takes_a_bare_fresh_generator_flag() {
    let function = krs_syntax::FunctionAttribute::parse_source(
        r#"total, fresh_generator, sort = Loc, syntax = "freshLoc({seed})""#,
    )
    .unwrap();
    assert_eq!(function.fresh_generator().unwrap(), "fresh_generator");
    assert!(
        function
            .provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::FunctionFreshGenerator)
    );
    let plain =
        krs_syntax::FunctionAttribute::parse_source(r#"total, sort = Int, syntax = "f({x})""#)
            .unwrap();
    assert!(plain.fresh_generator().is_none());
}

#[test]
fn fresh_generator_rejects_duplicates_values_and_constructors() {
    let function_cases = [
        (
            r#"total, fresh_generator, fresh_generator, sort = Loc, syntax = "f({x})""#,
            SyntaxErrorKind::DuplicateArgument {
                name: "fresh_generator",
            },
        ),
        (
            r#"total, fresh_generator = true, sort = Loc, syntax = "f({x})""#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "fresh_generator",
                expected: "a bare flag in `#[k::function]`",
            },
        ),
    ];
    for (source, expected) in function_cases {
        let error = krs_syntax::FunctionAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
    let constructor = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Loc, syntax = "x", fresh_generator"#,
    )
    .unwrap_err();
    assert_eq!(
        constructor.kind(),
        &SyntaxErrorKind::UnknownArgument {
            name: "fresh_generator".to_owned(),
        }
    );
}

#[test]
fn fresh_binders_are_result_scoped_and_keep_their_helper() {
    let rule = krs_syntax::RuleItem::parse_source(
        "#[k::fresh(l: Loc)] fn alloc(term![Alloc()]: k::Term<Stmt>) -> k::Term<Stmt> { Holds(l) }",
    )
    .unwrap();
    let fresh = rule
        .existentials()
        .fresh()
        .iter()
        .map(|binder| binder.name().to_string())
        .collect::<Vec<_>>();
    assert_eq!(fresh, ["l"]);
    assert!(rule.existentials().binders().is_empty());
    assert_eq!(rule.existentials().attributes().len(), 1);
    assert!(rule.item().attrs.is_empty());
    let roles = rule
        .full_provenance()
        .unwrap()
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect::<Vec<_>>();
    for role in [
        ProvenanceRole::RuleFreshBinder,
        ProvenanceRole::RuleFreshBinderName,
        ProvenanceRole::RuleFreshBinderSort,
    ] {
        assert!(roles.contains(&role), "{role:?}");
    }
}

#[test]
fn fresh_binders_reject_matching_requires_repetition_and_disuse() {
    let position = |source: &str| {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        assert!(
            matches!(error.kind(), SyntaxErrorKind::FreshBinderPosition { .. }),
            "{source}: {:?}",
            error.kind()
        );
        assert_eq!(
            error.kind().code().as_str(),
            "krs::analysis::fresh-binder-position"
        );
    };
    position(
        "#[k::fresh(l: Loc)] fn a(term![Wrap(l)]: k::Term<Stmt>) -> k::Term<Stmt> { Holds(l) }",
    );
    position(
        "#[k::requires(is_loc(l))] #[k::fresh(l: Loc)] \
         fn a(term![Alloc()]: k::Term<Stmt>) -> k::Term<Stmt> { Holds(l) }",
    );
    position(
        "#[k::fresh(l: Loc)] fn a(term![Alloc()]: k::Term<Stmt>) -> k::Term<Stmt> { Alloc() }",
    );
    position(
        "#[k::exists(l: Loc)] #[k::fresh(l: Loc)] \
         fn a(term![Alloc()]: k::Term<Stmt>) -> k::Term<Stmt> { Holds(l) }",
    );
    let repeated = krs_syntax::RuleItem::parse_source(
        "#[k::fresh(l: Loc)] #[k::fresh(m: Loc)] \
         fn a(term![Alloc()]: k::Term<Stmt>) -> k::Term<Stmt> { Pair(l, m) }",
    )
    .unwrap_err();
    assert!(matches!(
        repeated.kind(),
        SyntaxErrorKind::UnsupportedRuleSignature { .. }
    ));
}
