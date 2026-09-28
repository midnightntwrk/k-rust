//! Simple rule signature, pattern, and result parser tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, RulePattern, SyntaxErrorKind, TermSymbolKind};

#[test]
fn term_macro_rule_preserves_signature_references_and_roles() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn step(term![model::Foo(value)]: k::Term<dyn model::Expr>) \
         -> k::Term<dyn model::Expr> { term![model::Bar(value)] }",
    )
    .unwrap();
    assert!(matches!(
        &rule.parameter().pattern,
        RulePattern::TermMacro { .. }
    ));
    assert_eq!(rule.parameter().term_sort.sort_spelling(), "model :: Expr");
    assert!(rule.parameter().term_sort.is_dynamic());
    assert_eq!(rule.result().symbols().len(), 2);

    let anchors = rule.provenance().unwrap();
    let roles = anchors
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect::<Vec<_>>();
    assert_eq!(roles[0], ProvenanceRole::RuleDeclaration);
    assert_eq!(roles[1], ProvenanceRole::RulePattern);
    assert_eq!(roles[2], ProvenanceRole::RuleType);
    assert_eq!(roles[3], ProvenanceRole::RuleResultType);
    assert_eq!(roles[4], ProvenanceRole::RuleResult);
    assert_eq!(anchors[1].key().role(), ProvenanceRole::RulePattern);
    assert_eq!(anchors[2].key().role(), ProvenanceRole::RuleType);
    assert!(roles.contains(&ProvenanceRole::RuleLeftPath));
    assert!(roles.contains(&ProvenanceRole::RuleRightPath));
}

#[test]
fn native_tuple_and_record_constructor_rules_are_accepted() {
    let tuple = krs_syntax::RuleItem::parse_source(
        "pub fn reduce(model::Foo(value, _): Term<dyn model::Expr>) \
         -> Term<dyn model::Expr> { model::Bar(value) }",
    )
    .unwrap();
    assert!(matches!(
        &tuple.parameter().pattern,
        RulePattern::Native { .. }
    ));

    let record = krs_syntax::RuleItem::parse_source(
        "fn reduce(Foo { lhs, rhs: _ }: Term<Expr>) -> Term<Expr> \
         { Bar { value: lhs } }",
    )
    .unwrap();
    assert!(!record.parameter().term_sort.is_dynamic());
}

#[test]
fn typed_requires_preserves_complete_and_nested_provenance() {
    let source = r"
        #[k::requires(builtin::int::gt(value, 0))]
        fn guarded(Guarded { value }: Term<Expr>) -> Term<Expr> { Done }
    ";
    let rule = krs_syntax::RuleItem::parse_source(source).unwrap();
    let condition = rule.requires().expect("guard is retained as a term");
    assert_eq!(condition.term().symbols().len(), 2);

    let keys = condition
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.key())
        .collect::<Vec<_>>();
    assert_eq!(
        keys.iter()
            .map(|key| (key.role(), key.ordinal()))
            .collect::<Vec<_>>(),
        [
            (ProvenanceRole::RuleRequires, 0),
            (ProvenanceRole::RuleRequiresPath, 0),
            (ProvenanceRole::RuleRequiresPath, 1),
            (ProvenanceRole::RuleRequiresApplicationHead, 0),
            (ProvenanceRole::RuleRequiresReference, 0),
            (ProvenanceRole::RuleRequiresLiteral, 0),
        ]
    );

    let references = rule
        .term_reference_candidates()
        .unwrap()
        .into_iter()
        .filter(|candidate| {
            candidate
                .key()
                .role()
                .as_str()
                .starts_with(ProvenanceRole::RuleRequires.as_str())
        })
        .map(|candidate| (candidate.key().role(), candidate.path_spelling()))
        .collect::<Vec<_>>();
    assert_eq!(
        references,
        [(
            ProvenanceRole::RuleRequiresApplicationHead,
            "builtin :: int :: gt".into()
        )]
    );
}

#[test]
fn requires_rejects_host_literals_missing_payloads_and_duplicates() {
    for source in [
        "#[k::requires(true)] fn bad(Foo: Term<Expr>) -> Term<Expr> { Done }",
        "#[k::requires(\"true\")] fn bad(Foo: Term<Expr>) -> Term<Expr> { Done }",
        "#[k::requires] fn bad(Foo: Term<Expr>) -> Term<Expr> { Done }",
        "#[k::requires(is_ready(Foo))] #[k::requires(ok(Foo))] fn bad(Foo: Term<Expr>) -> Term<Expr> { Done }",
    ] {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        assert!(
            matches!(
                error.kind(),
                SyntaxErrorKind::UnsupportedRuleSignature { .. }
                    | SyntaxErrorKind::UnsupportedTermExpression { .. }
            ),
            "{source}: {error}"
        );
    }
}

#[test]
fn malformed_rule_signatures_are_rejected() {
    for source in [
        "fn zero() -> Term<Expr> { Done }",
        "fn two(Foo: Term<Expr>, Bar: Term<Expr>) -> Term<Expr> { Done }",
        "async fn async_rule(Foo: Term<Expr>) -> Term<Expr> { Done }",
        "fn generic<T>(Foo: Term<Expr>) -> Term<Expr> { Done }",
        "fn wrong_type(Foo: Expr) -> Term<Expr> { Done }",
        "fn no_result(Foo: Term<Expr>) { Done }",
    ] {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedRuleSignature { .. } | SyntaxErrorKind::InvalidTermType
        ));
    }
}

#[test]
fn malformed_rule_patterns_and_bodies_are_rejected() {
    let cases = [
        ("fn wild(_: Term<Expr>) -> Term<Expr> { Done }", "pattern"),
        (
            "fn range(0..=3: Term<Expr>) -> Term<Expr> { Done }",
            "pattern",
        ),
        (
            "fn rest(Foo { value, .. }: Term<Expr>) -> Term<Expr> { Done }",
            "pattern",
        ),
        (
            "fn other(other![Foo]: Term<Expr>) -> Term<Expr> { Done }",
            "macro",
        ),
        (
            "fn semicolon(Foo: Term<Expr>) -> Term<Expr> { Done; }",
            "body",
        ),
        (
            "fn statements(Foo: Term<Expr>) -> Term<Expr> { let x = Done; x }",
            "body",
        ),
        (
            "fn operator(Foo: Term<Expr>) -> Term<Expr> { lhs + rhs }",
            "term",
        ),
    ];
    for (source, expected) in cases {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        match expected {
            "pattern" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::UnsupportedRulePattern { .. }
            )),
            "macro" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::UnexpectedMacro { .. }
            )),
            "body" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::UnsupportedRuleBody { .. }
            )),
            "term" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::UnsupportedTermExpression { .. }
            )),
            _ => unreachable!(),
        }
    }
}

#[test]
fn repeated_rule_pattern_binders_are_one_binding_with_two_occurrences() {
    let cases = [
        (
            "fn native(Foo(value, value): Term<Expr>) -> Term<Expr> { Done }",
            false,
        ),
        (
            "fn term_pattern(term![Foo(value, value)]: Term<Expr>) -> Term<Expr> { Done }",
            true,
        ),
    ];

    for (source, is_term_pattern) in cases {
        let rule = krs_syntax::RuleItem::parse_source(source).unwrap();
        assert_eq!(rule.parameter().pattern.bindings(), ["value"]);
        assert_eq!(rule.parameter().pattern.term().is_some(), is_term_pattern);

        let occurrences = rule
            .full_provenance()
            .unwrap()
            .into_iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftReference)
            .count();
        assert_eq!(occurrences, 2);
    }
}

#[test]
fn term_rule_candidates_preserve_ast_ordinals_across_binding_gaps() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn step(\
            term![model::Foo(value, model::Unit)]: Term<dyn model::Expr>\
        ) -> Term<result::Expr> {\
            term![result::Wrap(value, model::Bar, Done)]\
        }",
    )
    .unwrap();

    assert_eq!(rule.parameter().pattern.bindings().len(), 1);
    assert_eq!(rule.parameter().pattern.bindings()[0], "value");
    let candidates = rule.reference_candidates().unwrap();
    let actual = candidates
        .iter()
        .map(|candidate| {
            (
                candidate.key().role(),
                candidate.key().ordinal(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        [
            (ProvenanceRole::RuleType, 0, "model :: Expr".into()),
            (ProvenanceRole::RuleResultType, 0, "result :: Expr".into()),
            (ProvenanceRole::RuleLeftPath, 0, "model :: Foo".into()),
            (ProvenanceRole::RuleLeftPath, 2, "model :: Unit".into()),
            (ProvenanceRole::RuleRightPath, 0, "result :: Wrap".into()),
            (ProvenanceRole::RuleRightPath, 2, "model :: Bar".into()),
            (ProvenanceRole::RuleRightPath, 3, "Done".into()),
        ]
    );

    let anchors = rule.provenance().unwrap();
    assert!(
        anchors.iter().any(|anchor| {
            anchor.role() == ProvenanceRole::RuleLeftPath && anchor.ordinal() == 1
        })
    );
    assert!(
        anchors.iter().any(|anchor| {
            anchor.role() == ProvenanceRole::RuleRightPath && anchor.ordinal() == 1
        })
    );
}

#[test]
fn native_rule_bindings_are_not_guessed_as_short_name_constructors() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn step(\
            model::Foo { value, marker: model::Unit }: Term<model::Expr>\
        ) -> Term<model::Expr> {\
            model::Bar(value, model::Done)\
        }",
    )
    .unwrap();
    assert_eq!(rule.parameter().pattern.bindings()[0], "value");

    let candidates = rule.reference_candidates().unwrap();
    let paths = candidates
        .iter()
        .map(|candidate| {
            (
                candidate.key().role(),
                candidate.key().ordinal(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert!(paths.contains(&(ProvenanceRole::RuleLeftPath, 0, "model :: Foo".into())));
    assert!(paths.contains(&(ProvenanceRole::RuleLeftPath, 2, "model :: Unit".into())));
    assert!(paths.contains(&(ProvenanceRole::RuleRightPath, 0, "model :: Bar".into())));
    assert!(paths.contains(&(ProvenanceRole::RuleRightPath, 2, "model :: Done".into())));
    assert!(!paths.iter().any(|(_, _, path)| path == "value"));
}

#[test]
fn native_binding_has_exact_compact_and_typed_left_provenance() {
    let source = "fn r(Add { lhs }: Term<Expr>) -> Term<Expr> { lhs }";
    let rule = krs_syntax::RuleItem::parse_source(source).unwrap();
    assert_eq!(rule.parameter().pattern.bindings(), ["lhs"]);

    let anchors = rule.full_provenance().unwrap();
    let left = anchors
        .iter()
        .filter(|anchor| {
            matches!(
                anchor.role(),
                ProvenanceRole::RuleLeftPath
                    | ProvenanceRole::RuleLeftApplicationHead
                    | ProvenanceRole::RuleLeftReference
            )
        })
        .map(|anchor| {
            (
                anchor.role(),
                anchor.ordinal(),
                anchor.range().start().column,
                anchor.range().end().column,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        left,
        [
            (ProvenanceRole::RuleLeftPath, 0, 5, 8),
            (ProvenanceRole::RuleLeftPath, 1, 11, 14),
            (ProvenanceRole::RuleLeftApplicationHead, 0, 5, 8),
            (ProvenanceRole::RuleLeftReference, 0, 11, 14),
        ]
    );

    let compact_candidates = rule
        .reference_candidates()
        .unwrap()
        .into_iter()
        .filter(|candidate| candidate.key().role() == ProvenanceRole::RuleLeftPath)
        .map(|candidate| (candidate.key().ordinal(), candidate.path_spelling()))
        .collect::<Vec<_>>();
    assert_eq!(compact_candidates, [(0, "Add".into())]);

    let typed_candidates = rule
        .term_reference_candidates()
        .unwrap()
        .into_iter()
        .filter(|candidate| candidate.key().role().as_str().starts_with("rule_left_"))
        .map(|candidate| {
            (
                candidate.key().role(),
                candidate.key().ordinal(),
                candidate.kind(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        typed_candidates,
        [(
            ProvenanceRole::RuleLeftApplicationHead,
            0,
            TermSymbolKind::ApplicationHead,
            "Add".into(),
        )]
    );
}

#[test]
fn nested_reordered_native_records_retain_binding_preorder() {
    let source = "fn nested(Outer { rhs: Pair { second: right, first: Left(left) }, lhs }: \
                  Term<Expr>) -> Term<Expr> { lhs }";
    let rule = krs_syntax::RuleItem::parse_source(source).unwrap();
    assert_eq!(
        rule.parameter().pattern.bindings(),
        ["right", "left", "lhs"]
    );

    let anchors = rule.full_provenance().unwrap();
    let compact_left = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftPath)
        .map(|anchor| {
            (
                anchor.ordinal(),
                &source[anchor.range().start().column..anchor.range().end().column],
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        compact_left,
        [
            (0, "Outer"),
            (1, "Pair"),
            (2, "right"),
            (3, "Left"),
            (4, "left"),
            (5, "lhs"),
        ]
    );

    let typed_left = anchors
        .iter()
        .filter(|anchor| {
            matches!(
                anchor.role(),
                ProvenanceRole::RuleLeftApplicationHead | ProvenanceRole::RuleLeftReference
            )
        })
        .map(|anchor| {
            (
                anchor.role(),
                anchor.ordinal(),
                &source[anchor.range().start().column..anchor.range().end().column],
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        typed_left,
        [
            (ProvenanceRole::RuleLeftApplicationHead, 0, "Outer"),
            (ProvenanceRole::RuleLeftApplicationHead, 1, "Pair"),
            (ProvenanceRole::RuleLeftReference, 0, "right"),
            (ProvenanceRole::RuleLeftApplicationHead, 2, "Left"),
            (ProvenanceRole::RuleLeftReference, 1, "left"),
            (ProvenanceRole::RuleLeftReference, 2, "lhs"),
        ]
    );
}

#[test]
fn native_resolution_candidates_keep_binding_ordinal_gaps() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn gaps(Outer(first, model::Unit, second, model::Done): Term<Expr>) -> Term<Expr> { \
         Result(first, model::Keep, second, model::End) }",
    )
    .unwrap();

    let compact = rule
        .reference_candidates()
        .unwrap()
        .into_iter()
        .filter(|candidate| {
            matches!(
                candidate.key().role(),
                ProvenanceRole::RuleLeftPath | ProvenanceRole::RuleRightPath
            )
        })
        .map(|candidate| {
            (
                candidate.key().role(),
                candidate.key().ordinal(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        compact,
        [
            (ProvenanceRole::RuleLeftPath, 0, "Outer".into()),
            (ProvenanceRole::RuleLeftPath, 2, "model :: Unit".into()),
            (ProvenanceRole::RuleLeftPath, 4, "model :: Done".into()),
            (ProvenanceRole::RuleRightPath, 0, "Result".into()),
            (ProvenanceRole::RuleRightPath, 2, "model :: Keep".into()),
            (ProvenanceRole::RuleRightPath, 4, "model :: End".into()),
        ]
    );

    let typed = rule
        .term_reference_candidates()
        .unwrap()
        .into_iter()
        .map(|candidate| {
            (
                candidate.key().role(),
                candidate.key().ordinal(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        typed,
        [
            (ProvenanceRole::RuleLeftApplicationHead, 0, "Outer".into()),
            (ProvenanceRole::RuleLeftReference, 1, "model :: Unit".into()),
            (ProvenanceRole::RuleLeftReference, 3, "model :: Done".into()),
            (ProvenanceRole::RuleRightApplicationHead, 0, "Result".into()),
            (
                ProvenanceRole::RuleRightReference,
                1,
                "model :: Keep".into()
            ),
            (ProvenanceRole::RuleRightReference, 3, "model :: End".into()),
        ]
    );
}

#[test]
fn bare_root_unit_constructor_is_a_reference_not_a_binding() {
    let rule =
        krs_syntax::RuleItem::parse_source("fn stay(Done: Term<Expr>) -> Term<Expr> { Done }")
            .unwrap();
    assert!(rule.parameter().pattern.bindings().is_empty());

    let candidates = rule.reference_candidates().unwrap();
    assert!(candidates.iter().any(|candidate| {
        candidate.key().role() == ProvenanceRole::RuleLeftPath
            && candidate.key().ordinal() == 0
            && candidate.path_spelling() == "Done"
    }));
    assert!(candidates.iter().any(|candidate| {
        candidate.key().role() == ProvenanceRole::RuleRightPath
            && candidate.key().ordinal() == 0
            && candidate.path_spelling() == "Done"
    }));
}
