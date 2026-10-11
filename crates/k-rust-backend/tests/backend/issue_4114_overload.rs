//! The critical-pair check on an overload family whose generated `symbol-overload` axiom and a
//! written equation do not join: K's issue-4114 regression test, trimmed
//! (`tests/fixtures/issue-4114-overload.kore`). The full compiled definition is a case of the
//! corpus gate (`scripts/value-contract-corpus.toml`, `issue-4114`), which needs the conformance
//! driver; this fixture pins the same pair on every push.

use k_rust_backend::{
    confluence::UnjoinedReason, definition::BackendDefinition, externalize, term::Term,
};
use k_rust_kore::kore::parser::parse_definition;

const TEST_BAR: &str = "Lbltest'LParUndsRParUnds'TEST'Unds'Bool'Unds'Bar";
const TEST_FOO: &str = "Lbltest'LParUndsRParUnds'TEST'Unds'Bool'Unds'Foo";

fn definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/issue-4114-overload.kore"))
        .expect("issue-4114 fixture should parse");
    BackendDefinition::internalize(&syntax, "ISSUE-4114")
        .expect("issue-4114 fixture should internalize")
}

fn show(term: &Term) -> String {
    externalize::term(term).to_string()
}

/// `test(_) => false` is sorted at `test(Bar)`, so it applies to `test(Bar)(inj(foo))`, which the
/// overload axiom equates with `test(Foo)(foo)`, which `test(foo) => true` rewrites to `true`.
/// The two reducts of the overlap, `test(Foo)(K0)` and `false`, do not join, and that one pair
/// withdraws the claims of both overloaded symbols: the warning the definition's users see.
#[test]
fn the_overload_axiom_and_the_catch_all_equation_are_the_one_pair_that_withdraws_claims() {
    let definition = definition();
    let claims = definition.value_claims();
    let counts = claims.counts();
    assert_eq!(
        (
            counts.equations,
            counts.pairs,
            counts.unjoined,
            counts.families
        ),
        (3, 1, 1, 1),
        "{counts:?}"
    );
    let relevant = claims
        .unjoined()
        .iter()
        .filter(|pair| pair.relevant())
        .collect::<Vec<_>>();
    let [pair] = relevant.as_slice() else {
        panic!("expected one relevant pair: {:?}", claims.unjoined());
    };

    // The first equation is the frontend's generated overload axiom: no source location.
    assert!(
        pair.first
            .attributes
            .origins
            .iter()
            .all(|origin| origin.location.is_none()),
        "{:?}",
        pair.first.attributes.origins
    );
    assert_eq!(
        show(&pair.first.lhs),
        format!("{TEST_BAR}{{}}(inj{{SortFoo{{}}, SortBar{{}}}}(Eq-hK0:SortFoo{{}}))")
    );
    // The second is `rule test(_) => false` (test.k line 11).
    assert_eq!(
        pair.second.attributes.unique_id,
        "eb5193032115bb030f05af2bc1c4c32bd5a59130715305250ea6015f3b056043"
    );
    assert_eq!(
        pair.second
            .attributes
            .origins
            .iter()
            .map(|origin| origin.location.as_deref())
            .collect::<Vec<_>>(),
        [Some("Location(11,3,11,26)")]
    );

    assert!(pair.position.is_empty(), "the overlap is at the root");
    assert_eq!(pair.overlap.as_ref().map(show), Some(show(&pair.first.lhs)));
    let (left, right) = pair.sides.as_ref().expect("both reducts");
    assert_eq!(
        (left.as_ref().map(show), right.as_ref().map(show)),
        (
            Some(format!("{TEST_FOO}{{}}(Eq-hK0:SortFoo{{}})")),
            Some("\\dv{SortBool{}}(\"false\")".to_owned())
        )
    );
    assert_eq!(pair.reason, UnjoinedReason::DifferentResults);
    assert_eq!(
        pair.withdrawn
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        [TEST_BAR, TEST_FOO]
    );
}
