//! `concrete`, `symbolic`, and `smt_lemma` keys of `#[k::equation]` and
//! `#[k::simplification]` (KF-043).

use krs_syntax::{KrsSyntax, MatchRestriction, ProvenanceRole, SyntaxErrorKind};

fn listed(restriction: &MatchRestriction, concrete: bool) -> Option<Vec<String>> {
    let key = if concrete {
        restriction.concrete()
    } else {
        restriction.symbolic()
    }?;
    Some(key.variables().map_or_else(Vec::new, |variables| {
        variables.iter().map(ToString::to_string).collect()
    }))
}

fn roles(anchors: &[krs_syntax::ProvenanceAnchor]) -> Vec<(ProvenanceRole, u32)> {
    anchors
        .iter()
        .map(|anchor| (anchor.role(), anchor.ordinal()))
        .collect()
}

#[test]
fn simplification_accepts_priority_and_restrictions_in_any_order() {
    let parsed = krs_syntax::SimplificationAttribute::parse_source(
        "priority = 40, concrete(c), symbolic(s, t), smt_lemma",
    )
    .unwrap();
    assert_eq!(parsed.priority(), Some(40));
    let restriction = parsed.restriction();
    assert_eq!(listed(restriction, true), Some(vec!["c".into()]));
    assert_eq!(
        listed(restriction, false),
        Some(vec!["s".into(), "t".into()])
    );
    assert!(restriction.smt_lemma().is_some());
    assert_eq!(
        roles(&parsed.provenance().unwrap()),
        [
            (ProvenanceRole::SimplificationPriority, 0),
            (ProvenanceRole::RestrictionConcrete, 0),
            (ProvenanceRole::RestrictionVariable, 0),
            (ProvenanceRole::RestrictionSymbolic, 0),
            (ProvenanceRole::RestrictionVariable, 1),
            (ProvenanceRole::RestrictionVariable, 2),
            (ProvenanceRole::SmtLemma, 0),
        ]
    );

    let reordered =
        krs_syntax::SimplificationAttribute::parse_source("smt_lemma, concrete(x)").unwrap();
    assert_eq!(
        listed(reordered.restriction(), true),
        Some(vec!["x".into()])
    );
    assert!(reordered.restriction().symbolic().is_none());
}

#[test]
fn equation_accepts_bare_restrictions_beside_its_priority() {
    let parsed = krs_syntax::EquationAttribute::parse_source("concrete, smt_lemma").unwrap();
    let restriction = parsed.restriction();
    assert_eq!(listed(restriction, true), Some(Vec::new()));
    assert!(restriction.concrete().unwrap().variables().is_none());
    assert!(restriction.smt_lemma().is_some());
    assert_eq!(
        roles(&parsed.provenance().unwrap()),
        [
            (ProvenanceRole::RestrictionConcrete, 0),
            (ProvenanceRole::SmtLemma, 0),
        ]
    );

    let ordered = krs_syntax::EquationAttribute::parse_source("owise, symbolic").unwrap();
    assert!(ordered.is_owise());
    assert!(ordered.restriction().symbolic().is_some());

    let plain = krs_syntax::EquationAttribute::parse_source("priority = 40").unwrap();
    assert!(plain.restriction().is_empty());
}

#[test]
fn malformed_restrictions_are_rejected() {
    for (source, expected) in [
        (
            "concrete, concrete(x)",
            "`concrete` is written bare (every binder) or with a list of binders, not both",
        ),
        (
            "symbolic(x), symbolic",
            "`symbolic` is written bare (every binder) or with a list of binders, not both",
        ),
        (
            "concrete()",
            "`concrete()` lists no binder; write bare `concrete` to restrict every binder",
        ),
        ("concrete(x, x)", "`x` is listed twice in `concrete(..)`"),
        (
            "concrete = x",
            "`concrete` takes no value; write bare `concrete` for every binder or `concrete(x, ..)` for some",
        ),
        (
            "smt_lemma = true",
            "`smt_lemma` is a bare flag; write `smt_lemma` without a value",
        ),
    ] {
        for parsed in [
            krs_syntax::SimplificationAttribute::parse_source(source).map(|_| ()),
            krs_syntax::EquationAttribute::parse_source(source).map(|_| ()),
        ] {
            let error = parsed.unwrap_err();
            assert_eq!(
                error.kind(),
                &SyntaxErrorKind::InvalidMatchRestriction {
                    reason: expected.into()
                },
                "{source}"
            );
            assert_eq!(
                error.kind().code().as_str(),
                "krs::syntax::invalid-match-restriction"
            );
        }
    }
    for (source, name) in [
        ("concrete, concrete", "concrete"),
        ("symbolic(x), symbolic(y)", "symbolic"),
        ("smt_lemma, smt_lemma", "smt_lemma"),
    ] {
        let error = krs_syntax::SimplificationAttribute::parse_source(source).unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::DuplicateArgument { name },
            "{source}"
        );
    }
}

#[test]
fn restrictions_on_a_transition_rule_point_to_equations_and_simplifications() {
    for source in ["concrete", "symbolic(x)", "smt_lemma"] {
        let error = krs_syntax::RuleAttribute::parse_source(source).unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::InvalidRuleKey {
                reason: "restrictions apply to equations and simplifications: `concrete`, `symbolic`, and `smt_lemma` are keys of #[k::equation] and #[k::simplification]",
            },
            "{source}"
        );
    }
}
