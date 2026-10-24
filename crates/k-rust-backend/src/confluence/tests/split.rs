//! F2's coverage (`join.rs`, `Sorts::constructors_covering`) against K's parametric `ite{S}`
//! (FZ-CONFLUENCE-F review, B1). `hTc(X) = c0` beside `hTc(X) = pTc(X)`, with the partial
//! `pTc(tc1) = pTc(tc2) = c0`, joins when `tc1` and `tc2` build every element of `Tc`. With
//! `ite{S}` declared and a total `pB : Tc -> Bool` without equations, `ite(pB(tc1), tc1, tc2)` is
//! a normal form of `Tc` that no constructor builds (a stuck total application of sort `Bool` is
//! a normal form, not a literal), at which `pTc` is stuck: `hTc` there is `c0` by one equation and
//! `\bottom` by the other, so the pair must stay named.

use k_rust_kore::kore::parser::parse_definition;

use crate::{confluence::CheckScope, definition::BackendDefinition};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    sort SortTc{} []
    sort SortA{} []
    symbol inj{From, To}(From) : To [sortInjection{}()]
    symbol c0{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
    symbol tc1{}() : SortTc{} [constructor{}(), functional{}(), injective{}()]
    symbol tc2{}() : SortTc{} [constructor{}(), functional{}(), injective{}()]
    symbol pTc{}(SortTc{}) : SortA{} [function{}()]
    symbol hTc{}(SortTc{}) : SortA{} [anywhere{}()]
"#;

const ITE: &str = r#"
    hooked-symbol ite{S}(SortBool{}, S, S) : S [function{}(), total{}(), hook{}("KEQUAL.ite")]
"#;

const STUCK_BOOL: &str = "symbol pB{}(SortTc{}) : SortBool{} [function{}(), total{}()]";

/// `head(X0) = right` with `X0` matching `pattern`, labelled `id`.
fn equation(head: &str, pattern: &str, right: &str, id: &str, attributes: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortTc{{}}, R}}(X0:SortTc{{}}, {pattern}), \top{{R}}())),
            \equals{{SortA{{}}, R}}({head}{{}}(X0:SortTc{{}}), \and{{SortA{{}}}}({right}, \top{{SortA{{}}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}"){attributes}]"#
    )
}

/// The full check's non-joined pairs of the definition with `declarations` added.
fn unjoined(declarations: &str) -> usize {
    let axioms = [
        equation("hTc", "VarX:SortTc{}", "c0{}()", "hc", ", anywhere{}()"),
        equation(
            "hTc",
            "VarX:SortTc{}",
            "pTc{}(X0:SortTc{})",
            "hp",
            ", anywhere{}()",
        ),
        equation("pTc", "tc1{}()", "c0{}()", "p1", ""),
        equation("pTc", "tc2{}()", "c0{}()", "p2", ""),
    ];
    let source = format!(
        "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("the definition internalizes")
        .value_claims_in_scope(CheckScope::All)
        .unjoined()
        .len()
}

#[test]
fn ite_is_a_producer_at_every_sort_so_the_complement_stays() {
    assert_eq!(unjoined(""), 0, "the constructors cover Tc");
    assert_eq!(unjoined(&format!("{ITE} {STUCK_BOOL}")), 1);
    assert_eq!(unjoined(ITE), 1, "ite alone already disables the coverage");
}
