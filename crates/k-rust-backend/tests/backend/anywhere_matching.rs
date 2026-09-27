//! Matching against subject applications of `anywhere` productions (probe `stuckwrap.k`): such
//! an application is compared by its head and arguments only when no equation can rewrite any
//! of its instances; otherwise the pair stays in the remainder.

use k_rust_backend::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    simplify::{SimplificationOptions, simplify},
    substitution::Substitution,
    term::{Sort, Term, Variable},
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

/// `wrap` carries the anywhere equation `wrap(s(z)) = wrap(z)` and `into` the anywhere equation
/// `into(s(X)) = addr(X)`, both emitted with `\in` binders and the `injective` attribute as
/// kompile emits anywhere rules; `f` is a total function with the equation `f(wrap(z)) = done`.
fn definition() -> BackendDefinition {
    definition_with("")
}

/// [`definition`] with `attribute` (a KORE attribute, or empty) added to the `into` equation
/// `into(s(N)) = addr(N)`.
fn definition_with(attribute: &str) -> BackendDefinition {
    let attribute = if attribute.is_empty() {
        String::new()
    } else {
        format!(", {attribute}")
    };
    let source = format!(
        r#"[]
            module MAIN
                sort SortNat{{}} []
                sort SortW{{}} []
                symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol done{{}}() : SortW{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol addr{{}}(SortNat{{}}) : SortW{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol wrap{{}}(SortNat{{}}) : SortW{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                symbol into{{}}(SortNat{{}}) : SortW{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                symbol f{{}}(SortW{{}}) : SortW{{}} [function{{}}(), total{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, s{{}}(z{{}}())), \top{{R}}())
                    ),
                    \equals{{SortW{{}}, R}}(
                        wrap{{}}(X0:SortNat{{}}),
                        \and{{SortW{{}}}}(wrap{{}}(z{{}}()), \top{{SortW{{}}}}())
                    )
                ) [label{{}}("collapse"), anywhere{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, s{{}}(N:SortNat{{}})), \top{{R}}())
                    ),
                    \equals{{SortW{{}}, R}}(
                        into{{}}(X0:SortNat{{}}),
                        \and{{SortW{{}}}}(addr{{}}(N:SortNat{{}}), \top{{SortW{{}}}}())
                    )
                ) [label{{}}("into"), anywhere{{}}(){attribute}]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(\in{{SortW{{}}, R}}(X0:SortW{{}}, wrap{{}}(z{{}}())), \top{{R}}())
                    ),
                    \equals{{SortW{{}}, R}}(
                        f{{}}(X0:SortW{{}}),
                        \and{{SortW{{}}}}(done{{}}(), \top{{SortW{{}}}}())
                    )
                ) [label{{}}("fhit")]
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn matching(mode: MatchMode, pattern: &str, subject: &str) -> MatchResult {
    let definition = definition();
    match_terms_in_definition(
        mode,
        &definition,
        &internal_term(&definition, pattern),
        &internal_term(&definition, subject),
    )
}

const MODES: [MatchMode; 3] = [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies];

/// Match `pattern` against `subject` below the root in every mode: in `Evaluate` mode the root
/// is the application an equation is tried on, so both sides are placed under `f`.
fn nested(mode: MatchMode, pattern: &str, subject: &str) -> MatchResult {
    if mode == MatchMode::Evaluate {
        matching(
            mode,
            &format!("f{{}}({pattern})"),
            &format!("f{{}}({subject})"),
        )
    } else {
        matching(mode, pattern, subject)
    }
}

/// `wrap(s(X))` equals `wrap(z)` at `X = z`, so no mode refutes the pattern `wrap(z)` on it; the
/// ground redex `wrap(s(z))` is not refuted either.
#[test]
fn an_anywhere_application_an_equation_reaches_is_not_refuted() {
    for mode in MODES {
        for subject in ["wrap{}(s{}(X:SortNat{}))", "wrap{}(s{}(z{}()))"] {
            let result = nested(mode, "wrap{}(z{}())", subject);
            assert!(
                matches!(result, MatchResult::Indeterminate { .. }),
                "{mode:?} {subject}: {result:?}"
            );
        }
    }
}

/// `wrap(X)` matches `wrap(z)` at `X = z` and at `X = s(z)`: the pair is not decomposed into the
/// binding-shaped remainder `z = X`, which would lose the second instance.
#[test]
fn an_anywhere_application_an_equation_reaches_is_not_decomposed() {
    for mode in MODES {
        let result = nested(mode, "wrap{}(z{}())", "wrap{}(X:SortNat{})");
        let MatchResult::Indeterminate { remainder, .. } = &result else {
            panic!("{mode:?}: {result:?}");
        };
        let definition = definition();
        assert_eq!(
            remainder,
            &[(
                internal_term(&definition, "wrap{}(z{}())"),
                internal_term(&definition, "wrap{}(X:SortNat{})"),
            )],
            "{mode:?}"
        );
    }
    // A pattern variable under the head is not bound through a subject that is not normal.
    let result = matching(
        MatchMode::Rewrite,
        "wrap{}(Y:SortNat{})",
        "wrap{}(s{}(X:SortNat{}))",
    );
    assert!(
        matches!(result, MatchResult::Indeterminate { .. }),
        "{result:?}"
    );
}

/// Applications that no equation rewrites keep the constructor reading, ground or symbolic.
#[test]
fn instance_normal_anywhere_applications_are_decided() {
    for subject in ["wrap{}(s{}(s{}(X:SortNat{})))", "wrap{}(s{}(s{}(z{}())))"] {
        let result = matching(MatchMode::Rewrite, "wrap{}(z{}())", subject);
        assert!(
            matches!(result, MatchResult::Failed(_)),
            "{subject}: {result:?}"
        );
    }
    assert_eq!(
        matching(MatchMode::Rewrite, "wrap{}(z{}())", "wrap{}(z{}())"),
        MatchResult::Success(Substitution::new())
    );
    let definition = definition();
    assert_eq!(
        matching(
            MatchMode::Rewrite,
            "wrap{}(Y:SortNat{})",
            "wrap{}(s{}(s{}(X:SortNat{})))"
        ),
        MatchResult::Success(Substitution::from([(
            Variable::new("Y", Sort::simple("SortNat")),
            internal_term(&definition, "s{}(s{}(X:SortNat{}))"),
        )]))
    );
}

/// `into(s(X))` equals `addr(X)`, so a different rigid pattern head does not refute it; an
/// application no equation rewrites keeps its own head.
#[test]
fn a_different_pattern_head_refutes_only_an_instance_normal_application() {
    for mode in MODES {
        let result = nested(mode, "addr{}(z{}())", "into{}(s{}(X:SortNat{}))");
        assert!(
            matches!(result, MatchResult::Indeterminate { .. }),
            "{mode:?}: {result:?}"
        );
    }
    for subject in ["into{}(z{}())", "wrap{}(s{}(s{}(X:SortNat{})))"] {
        let result = matching(MatchMode::Rewrite, "addr{}(z{}())", subject);
        assert!(
            matches!(result, MatchResult::Failed(_)),
            "{subject}: {result:?}"
        );
    }
}

/// Equation matching (probe `awf.k`): `f(wrap(z))` is not refuted on `f(wrap(s(X)))`, so the
/// `owise` equation cannot fire there, and is refuted on `f(wrap(s(s(X))))`. The equation's own
/// root is compared as it stands: the anywhere equation applies to the redex it names.
#[test]
fn equation_matching_compares_arguments_by_value_and_the_root_as_written() {
    let result = matching(
        MatchMode::Evaluate,
        "f{}(wrap{}(z{}()))",
        "f{}(wrap{}(s{}(X:SortNat{})))",
    );
    assert!(
        matches!(result, MatchResult::Indeterminate { .. }),
        "{result:?}"
    );
    let result = matching(
        MatchMode::Evaluate,
        "f{}(wrap{}(z{}()))",
        "f{}(wrap{}(s{}(s{}(X:SortNat{}))))",
    );
    assert!(matches!(result, MatchResult::Failed(_)), "{result:?}");
    assert_eq!(
        matching(
            MatchMode::Evaluate,
            "f{}(wrap{}(z{}()))",
            "f{}(wrap{}(z{}()))"
        ),
        MatchResult::Success(Substitution::new())
    );
    // The redex `wrap(s(z))` is not a normal form, yet an equation headed by `wrap` is tried
    // on it as written.
    let definition = definition();
    assert_eq!(
        matching(
            MatchMode::Evaluate,
            "wrap{}(s{}(N:SortNat{}))",
            "wrap{}(s{}(z{}()))"
        ),
        MatchResult::Success(Substitution::from([(
            Variable::new("N", Sort::simple("SortNat")),
            internal_term(&definition, "z{}()"),
        )]))
    );
    let result = matching(
        MatchMode::Evaluate,
        "wrap{}(s{}(z{}()))",
        "wrap{}(s{}(s{}(X:SortNat{})))",
    );
    assert!(matches!(result, MatchResult::Failed(_)), "{result:?}");
}

fn simplified(definition: &BackendDefinition, source: &str) -> Term {
    simplify(
        definition,
        &internal_term(definition, source),
        SimplificationOptions::default(),
    )
    .expect("the term should simplify")
    .term
}

/// A normal form the simplifier certified (its `evaluated` bit) keeps its head without the
/// equation scan: rewrite matching refutes a different head on it, rewrite and implication
/// matching refute different arguments, and a pattern variable binds through it, exactly as for
/// the unsimplified instance-normal term.
#[test]
fn a_certified_normal_form_is_decided_by_its_head_and_arguments() {
    let definition = definition();
    let subject = simplified(&definition, "wrap{}(s{}(s{}(z{}())))");
    assert!(subject.attributes().evaluated);
    for mode in [MatchMode::Rewrite, MatchMode::Implies] {
        let patterns: &[&str] = if mode == MatchMode::Rewrite {
            &["wrap{}(z{}())", "addr{}(z{}())"]
        } else {
            &["wrap{}(z{}())"]
        };
        for pattern in patterns {
            let result = match_terms_in_definition(
                mode,
                &definition,
                &internal_term(&definition, pattern),
                &subject,
            );
            assert!(
                matches!(result, MatchResult::Failed(_)),
                "{mode:?} {pattern}: {result:?}"
            );
        }
        assert_eq!(
            match_terms_in_definition(
                mode,
                &definition,
                &internal_term(&definition, "wrap{}(Y:SortNat{})"),
                &subject,
            ),
            MatchResult::Success(Substitution::from([(
                Variable::new("Y", Sort::simple("SortNat")),
                internal_term(&definition, "s{}(s{}(z{}()))"),
            )]))
        );
    }
}

/// With `into` marked `symbolic`, the evaluator does not rewrite the ground `into(s(z))`, but
/// the equation still makes it equal to `addr(z)`. The simplifier does not certify it, so
/// matching falls back to the equation scan and does not refute `addr(z)` on it.
#[test]
fn an_uncertified_simplifier_fixed_point_is_not_refuted() {
    let definition = definition_with("symbolic{}()");
    let subject = simplified(&definition, "into{}(s{}(z{}()))");
    assert_eq!(subject, internal_term(&definition, "into{}(s{}(z{}()))"));
    assert!(!subject.attributes().evaluated);
    let result = match_terms_in_definition(
        MatchMode::Rewrite,
        &definition,
        &internal_term(&definition, "addr{}(z{}())"),
        &subject,
    );
    assert!(
        matches!(result, MatchResult::Indeterminate { .. }),
        "{result:?}"
    );
}
