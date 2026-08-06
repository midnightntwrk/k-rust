use k_rust::kast::Term;

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
        });
    });

    assert_eq!(kinds, ["rewrite", "f", "X", "Y", "as", "Z", "A"]);
}
