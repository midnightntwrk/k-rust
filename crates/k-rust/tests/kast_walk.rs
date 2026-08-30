use k_rust::kast::{ResolvedProductionId, Sort, Term, TermMetadata, TermSpan};

#[test]
fn preorder_walk_visits_every_term_in_source_order() {
    let term = Term::Rewrite {
        left: Box::new(Term::apply(
            "f",
            vec![Term::variable("X"), Term::variable("Y")],
        )),
        right: Box::new(Term::As {
            pattern: Box::new(Term::variable("Z")),
            alias: Box::new(Term::variable("A")),
        }),
    };
    let mut kinds = Vec::new();
    term.visit_preorder(&mut |term| {
        kinds.push(match term {
            Term::Rewrite { .. } => "rewrite".into(),
            Term::As { .. } => "as".into(),
            Term::Variable { name, .. } => name.clone(),
            Term::Apply { label, .. } => label.name.clone(),
            Term::InjectedLabel(_) | Term::Sequence(_) | Term::Token { .. } => "other".into(),
            Term::Annotated { .. } => unreachable!("preorder traversal hides metadata wrappers"),
        });
    });

    assert_eq!(kinds, ["rewrite", "f", "X", "Y", "as", "Z", "A"]);
}

#[test]
fn metadata_is_semantically_transparent_but_remains_inspectable() {
    let plain = Term::apply("f", vec![Term::variable("X")]);
    let annotated = plain.clone().with_metadata(TermMetadata {
        span: Some(TermSpan {
            source: k_rust::provenance::SourceId(0),
            start: 2,
            end: 6,
        }),
        production: Some(ResolvedProductionId(7)),
        sort: Some(Sort::new("Exp")),
    });

    assert_eq!(annotated, plain);
    assert_eq!(format!("{annotated:?}"), format!("{plain:?}"));
    assert_eq!(annotated.to_string(), plain.to_string());
    assert_eq!(
        annotated.metadata(),
        Some(&TermMetadata {
            span: Some(TermSpan {
                source: k_rust::provenance::SourceId(0),
                start: 2,
                end: 6,
            }),
            production: Some(ResolvedProductionId(7)),
            sort: Some(Sort::new("Exp")),
        })
    );
}
