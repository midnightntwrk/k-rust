//! `unify_term_pairs` through the public API on `anywhere` productions: an equation between two
//! applications of an `anywhere` head is refuted only when no equation of the head can rewrite
//! an instance of either application.

use k_rust_backend::{
    definition::BackendDefinition,
    substitution::Substitution,
    unification::{UnificationFailure, UnificationResult, unify_term_pairs},
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

/// `wrap` carries the anywhere equation `wrap(s(z)) = wrap(z)`, emitted with an `\in` binder
/// and the `injective` attribute as kompile emits an anywhere rule.
fn definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol wrap{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [label{}("collapse"), anywhere{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn unify(left: &str, right: &str) -> UnificationResult {
    let definition = definition();
    let pair = (
        internal_term(&definition, left),
        internal_term(&definition, right),
    );
    unify_term_pairs(&definition, Substitution::new(), [pair])
}

/// The ground `wrap(s(z))` is not normalized; it equals `wrap(z)`, so the equation is kept.
#[test]
fn a_ground_anywhere_redex_is_not_refuted() {
    let result = unify("wrap{}(s{}(z{}()))", "wrap{}(z{}())");
    assert!(
        matches!(&result, UnificationResult::Unified(unified) if unified.constraints.len() == 1),
        "{result:?}"
    );
}

#[test]
fn a_symbolic_anywhere_application_an_equation_reaches_is_not_refuted() {
    let result = unify("wrap{}(s{}(X:SortNat{}))", "wrap{}(z{}())");
    assert!(
        matches!(&result, UnificationResult::Unified(unified) if unified.constraints.len() == 1),
        "{result:?}"
    );
}

#[test]
fn anywhere_applications_no_equation_reaches_are_refuted() {
    for left in ["wrap{}(s{}(s{}(X:SortNat{})))", "wrap{}(s{}(s{}(z{}())))"] {
        assert!(matches!(
            unify(left, "wrap{}(z{}())"),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_, _))
        ));
    }
}
