//! Hook pairs: an executable equation at a symbol whose hook the evaluator applies before any
//! equation, against the hook's written meaning (`confluence/hooks.rs`).

use k_rust_kore::kore::parser::parse_definition;

use super::super::{CheckScope, UnjoinedReason, ValueClaims};
use crate::definition::BackendDefinition;

/// `sel : Bool AB AB -> AB` hooked to `KEQUAL.ite`, `addAB : AB AB -> AB` hooked to `INT.add`
/// (evaluated, no written meaning), `opq : AB -> AB` hooked to a hook no evaluator implements,
/// the constructors `a` and `bb`, and `equations`.
fn definition(equations: &str) -> BackendDefinition {
    let source = format!(
        r#"[] module MAIN
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortAB{{}} []
            symbol a{{}}() : SortAB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol bb{{}}() : SortAB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            hooked-symbol sel{{}}(SortBool{{}}, SortAB{{}}, SortAB{{}}) : SortAB{{}}
                [function{{}}(), total{{}}(), hook{{}}("KEQUAL.ite")]
            hooked-symbol addAB{{}}(SortAB{{}}, SortAB{{}}) : SortAB{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add")]
            hooked-symbol opq{{}}(SortAB{{}}) : SortAB{{}} [function{{}}(), hook{{}}("ORACLE.function")]
            {equations}
        endmodule []"#
    );
    BackendDefinition::internalize(&parse_definition(&source).expect("parses"), "MAIN")
        .expect("internalizes")
}

/// The equation `head(X0, ..., Xn) = right` over the variables `variables` (`name:sort`),
/// labelled `label`.
fn equation(head: &str, variables: &[&str], right: &str, label: &str) -> String {
    let binders =
        variables
            .iter()
            .enumerate()
            .fold(r"\top{R}()".to_owned(), |rest, (index, variable)| {
                let sort = variable.split_once(':').expect("name:sort").1;
                format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {variable}), {rest})")
            });
    let arguments = variables
        .iter()
        .enumerate()
        .map(|(index, variable)| format!("X{index}:{}", variable.split_once(':').unwrap().1))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), {binders}),
            \equals{{SortAB{{}}, R}}({head}{{}}({arguments}), \and{{SortAB{{}}}}({right}, \top{{SortAB{{}}}}()))
        ) [label{{}}("{label}")]"#
    )
}

fn all(definition: &BackendDefinition) -> ValueClaims {
    definition.value_claims_in_scope(CheckScope::All)
}

/// r4-hookite: `sel(_, _, Y) = Y` disagrees with `KEQUAL.ite`, whose builtin gives
/// `sel(true, a, bb) = a`; the full check names it against the hook's first meaning.
#[test]
fn an_equation_that_disagrees_with_its_hook_is_named_against_the_hooks_meaning() {
    let definition = definition(&equation(
        "sel",
        &["B:SortBool{}", "X:SortAB{}", "Y:SortAB{}"],
        "Y:SortAB{}",
        "sel-last",
    ));
    let claims = all(&definition);
    let unjoined = claims.unjoined();
    assert_eq!(unjoined.len(), 1, "{unjoined:#?}");
    let pair = &unjoined[0];
    assert_eq!(pair.reason, UnjoinedReason::DifferentResults);
    assert_eq!(pair.hook.as_deref(), Some("KEQUAL.ite"));
    assert_eq!(pair.first.attributes.label.as_deref(), Some("sel-last"));
    assert_eq!(
        pair.second.attributes.label.as_deref(),
        Some("KEQUAL.ite meaning 1")
    );
    assert!(pair.reported());
    let counts = claims.counts();
    assert_eq!((counts.hook.equations, counts.hook.pairs), (1, 2));
    assert_eq!((counts.hook.not_joined, counts.hook.refuted), (1, 0));
    // Hook pairs are counted apart: the definition has no pair of its own equations.
    assert_eq!((counts.pairs, counts.overlaps, counts.unjoined), (0, 0, 1));
}

/// `sel(B, X, X) = X` is an identity of selection: both hook pairs join.
#[test]
fn an_equation_that_agrees_with_its_hook_joins_its_meaning() {
    // `X` binds both branches.
    let definition = definition(
        r#"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortBool{}, R}(X0:SortBool{}, B:SortBool{}),
                \and{R}(\in{SortAB{}, R}(X1:SortAB{}, X:SortAB{}), \and{R}(\in{SortAB{}, R}(X2:SortAB{}, X:SortAB{}), \top{R}())))),
            \equals{SortAB{}, R}(sel{}(X0:SortBool{}, X1:SortAB{}, X2:SortAB{}), \and{SortAB{}}(X:SortAB{}, \top{SortAB{}}()))
        ) [label{}("sel-same")]"#,
    );
    let claims = all(&definition);
    assert!(claims.unjoined().is_empty(), "{:#?}", claims.unjoined());
    let counts = claims.counts();
    assert_eq!((counts.hook.pairs, counts.hook.joined), (2, 2));
}

/// An equation at a hook the evaluator applies but the table writes no meaning for is reported
/// on its own, whatever the scope; an equation at a hook no evaluator implements is an ordinary
/// equation.
#[test]
fn an_unmodelled_hook_is_reported_and_an_unevaluated_one_is_not() {
    let definition = definition(&format!(
        "{} {}",
        equation(
            "addAB",
            &["X:SortAB{}", "Y:SortAB{}"],
            "X:SortAB{}",
            "add-left"
        ),
        equation("opq", &["X:SortAB{}"], "X:SortAB{}", "opq-id"),
    ));
    for claims in [definition.value_claims().clone(), all(&definition)] {
        let unjoined = claims.unjoined();
        assert_eq!(unjoined.len(), 1, "{unjoined:#?}");
        assert_eq!(
            unjoined[0].reason,
            UnjoinedReason::UnmodelledHook("INT.add".into())
        );
        assert!(unjoined[0].reason.describes_one_equation());
        assert_eq!(
            unjoined[0].first.attributes.label.as_deref(),
            Some("add-left")
        );
        let counts = claims.counts();
        assert_eq!(
            (
                counts.hook.equations,
                counts.hook.unevaluated,
                counts.hook.unmodelled
            ),
            (2, 1, 1)
        );
    }
}

/// The load's scope pairs an equation with its hook's meaning only where the equation is
/// relevant: `sel`'s equation reaches no symbol the gate is asked about, so the load names no
/// hook pair, and the full check does.
#[test]
fn the_load_pairs_only_relevant_equations_with_their_hooks() {
    let definition = definition(&equation(
        "sel",
        &["B:SortBool{}", "X:SortAB{}", "Y:SortAB{}"],
        "Y:SortAB{}",
        "sel-last",
    ));
    assert!(definition.value_claims().unjoined().is_empty());
    assert_eq!(all(&definition).unjoined().len(), 1);
}

/// FUN's prelude holds every equation of `domains.md` at a hooked symbol: each one at an
/// evaluated hook joins every equation of its hook's meaning.
#[test]
fn the_preludes_hooked_equations_join_their_hooks_meanings() {
    let source = include_str!("../../../tests/fixtures/fun-prelude-hooked-equations.kore");
    let definition =
        BackendDefinition::internalize(&parse_definition(source).expect("parses"), "FUN-UNTYPED")
            .expect("internalizes");
    let claims = all(&definition);
    let named = claims
        .unjoined()
        .iter()
        .filter(|pair| {
            pair.hook.is_some() || matches!(pair.reason, UnjoinedReason::UnmodelledHook(_))
        })
        .collect::<Vec<_>>();
    assert!(named.is_empty(), "{named:#?}");
    let counts = claims.counts();
    assert!(counts.hook.pairs > 0, "{counts:?}");
    assert_eq!(counts.hook.not_joined, 0);
    assert_eq!(counts.hook.unmodelled, 0);
}
