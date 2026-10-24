//! Overlaps over a sort with no normal form (FZ-EMPTYSORT; the FZ-DATAEND review's round-4
//! repros `r4-empty` and `r4-partnorule`). No evaluation reaches such an overlap, but every model
//! of the definition has an element of the sort, at which both equations hold, so the check sets
//! no such overlap aside, under either scope: it is refuted, joined or not joined like any other,
//! and a non-joined one names the sort. It withdraws no claim: the claims are read in `M_NF`,
//! where the sort is empty.

use k_rust_kore::kore::parser::parse_definition;

use crate::{
    confluence::{CheckScope, UnjoinedReason, ValueClaims},
    definition::BackendDefinition,
};

/// `A, B < AB`, the constructors `a : A` and `bb : B`, a total identity `id` on `AB`, and the
/// sort `S`, which `extra` may give symbols.
const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortA{} []
    sort SortB{} []
    sort SortAB{} []
    sort SortS{} []
    symbol inj{From, To}(From) : To [sortInjection{}()]
    axiom{R} \exists{R}(V:SortAB{}, \equals{SortAB{}, R}(V:SortAB{}, inj{SortA{}, SortAB{}}(F:SortA{}))) [subsort{SortA{}, SortAB{}}()]
    axiom{R} \exists{R}(V:SortAB{}, \equals{SortAB{}, R}(V:SortAB{}, inj{SortB{}, SortAB{}}(F:SortB{}))) [subsort{SortB{}, SortAB{}}()]
    symbol a{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
    symbol bb{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
    symbol id{}(SortAB{}) : SortAB{} [function{}(), total{}()]
"#;

const A: &str = r"inj{SortA{}, SortAB{}}(a{}())";
const BB: &str = r"inj{SortB{}, SortAB{}}(bb{}())";

/// `head(X0:sort) = right`, labelled `id`, with `attributes` besides its label.
fn equation(
    head: &str,
    sort: &str,
    result: &str,
    right: &str,
    id: &str,
    attributes: &str,
) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{sort}, R}}(X0:{sort}, Var{id}:{sort}), \top{{R}}())),
            \equals{{{result}, R}}({head}{{}}(X0:{sort}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}"){attributes}]"#
    )
}

/// The definition of `PRELUDE`, `declarations` and `axioms` at module `MAIN`.
fn load(declarations: &str, axioms: &[String]) -> BackendDefinition {
    let source = format!(
        "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    super::internalized(&syntax)
}

/// `f(_:S) => a` beside `f(_:S) => bb`, `f` total (`r4-empty` with `S` declared and nothing
/// else, `r4-partnorule` with `S ::= g(Int) [function]` and no equation of `g`).
fn f_a_and_bb(s_symbols: &str) -> BackendDefinition {
    load(
        &format!("symbol f{{}}(SortS{{}}) : SortAB{{}} [function{{}}(), total{{}}()] {s_symbols}"),
        &[
            equation("f", "SortS{}", "SortAB{}", A, "fa", ""),
            equation("f", "SortS{}", "SortAB{}", BB, "fbb", ""),
        ],
    )
}

const NOTHING: &str = "";
const PARTIAL_NO_RULE: &str = "symbol g{}(SortInt{}) : SortS{} [function{}()]";

/// The reasons of `claims`' non-joined pairs.
fn reasons(claims: &ValueClaims) -> Vec<UnjoinedReason> {
    claims
        .unjoined()
        .iter()
        .map(|pair| pair.reason.clone())
        .collect()
}

fn over_s(reason: UnjoinedReason) -> UnjoinedReason {
    UnjoinedReason::UninhabitedSort {
        sort: "SortS".into(),
        reason: Box::new(reason),
    }
}

/// `r4-empty` and `r4-partnorule`: the full check reports the pair, naming `S`, and counts its
/// overlap as one over a sort with no normal form (before FZ-EMPTYSORT it was "separated" and
/// nothing was reported, so `krust fuzz` killed `a` on `bb`).
#[test]
fn the_full_check_reports_a_pair_over_a_sort_with_no_normal_form() {
    for (name, symbols) in [("r4-empty", NOTHING), ("r4-partnorule", PARTIAL_NO_RULE)] {
        let definition = f_a_and_bb(symbols);
        let full = definition.value_claims_in_scope(CheckScope::All);
        assert_eq!(
            reasons(&full),
            [over_s(UnjoinedReason::DifferentResults)],
            "{name}"
        );
        let counts = full.counts();
        assert_eq!(
            (
                counts.overlaps,
                counts.uninhabited,
                counts.joined,
                counts.unjoined
            ),
            (1, 1, 0, 1),
            "{name}: {counts:?}"
        );
        let message = full.unjoined()[0].reason.to_string();
        assert!(
            message.starts_with("the two reducts reach different terms, at an overlap over `SortS`, a sort with no normal form"),
            "{name}: {message}"
        );
    }
}

/// The same pair at an equation head (`h(_:S) => a`, `h(_:S) => bb`, `anywhere`): the load's
/// scope classifies and lists it too, naming `S`, but it withdraws no claim in either scope (the
/// claims are read in `M_NF`, where it has no instance), so the scopes admit the same claims.
#[test]
fn a_pair_over_a_sort_with_no_normal_form_is_listed_by_both_scopes_and_withdraws_nothing() {
    for (name, symbols) in [("empty", NOTHING), ("partial", PARTIAL_NO_RULE)] {
        let definition = load(
            &format!("symbol h{{}}(SortS{{}}) : SortAB{{}} [anywhere{{}}()] {symbols}"),
            &[
                equation("h", "SortS{}", "SortAB{}", A, "ha", ", anywhere{}()"),
                equation("h", "SortS{}", "SortAB{}", BB, "hbb", ", anywhere{}()"),
            ],
        );
        let full = definition.value_claims_in_scope(CheckScope::All);
        for (scope, claims) in [
            (CheckScope::Gate, definition.value_claims()),
            (CheckScope::All, &full),
        ] {
            assert_eq!(
                reasons(claims),
                [over_s(UnjoinedReason::DifferentResults)],
                "{name} {scope:?}"
            );
            let pair = &claims.unjoined()[0];
            assert!(pair.over_uninhabited_sort(), "{name} {scope:?}");
            assert!(
                !pair.relevant() && !pair.reported(),
                "{name} {scope:?}: {pair:?}"
            );
            assert!(claims.tainted_symbols().is_empty(), "{name} {scope:?}");
            assert_eq!(claims.counts().uninhabited, 1, "{name} {scope:?}");
        }
        assert_eq!(
            definition
                .value_claims()
                .claim_differences(&full, &definition),
            Vec::<String>::new(),
            "{name}"
        );
    }
}

/// An overlap over a sort with no normal form whose reducts join (`f(_:S) => a` beside
/// `f(_:S) => id(a)`) is reported by neither scope: vacuity was never needed for it.
#[test]
fn a_pair_over_a_sort_with_no_normal_form_whose_reducts_join_is_not_reported() {
    for (name, symbols) in [("empty", NOTHING), ("partial", PARTIAL_NO_RULE)] {
        let definition = load(
            &format!(
                "symbol f{{}}(SortS{{}}) : SortAB{{}} [function{{}}(), total{{}}()] {symbols}"
            ),
            &[
                equation("f", "SortS{}", "SortAB{}", A, "fa", ""),
                equation(
                    "f",
                    "SortS{}",
                    "SortAB{}",
                    &format!("id{{}}({A})"),
                    "fida",
                    "",
                ),
                equation("id", "SortAB{}", "SortAB{}", "Varidx:SortAB{}", "idx", ""),
            ],
        );
        for scope in [CheckScope::Gate, CheckScope::All] {
            let claims = definition.value_claims_in_scope(scope);
            assert!(
                claims.unjoined().is_empty(),
                "{name} {scope:?}: {:?}",
                reasons(&claims)
            );
        }
        let counts = definition.value_claims_in_scope(CheckScope::All).counts();
        assert_eq!(
            (counts.overlaps, counts.uninhabited, counts.joined),
            (1, 1, 1),
            "{name}: {counts:?}"
        );
    }
}

/// With `g` declared `total`, `S` has a normal form (`g(0)`): the pair is reported, and its
/// reason names no sort.
#[test]
fn a_pair_over_an_inhabited_sort_names_no_sort() {
    let definition = f_a_and_bb("symbol g{}(SortInt{}) : SortS{} [function{}(), total{}()]");
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(reasons(&full), [UnjoinedReason::DifferentResults]);
    assert_eq!(full.counts().uninhabited, 0);
}
