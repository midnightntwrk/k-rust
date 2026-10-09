//! The load's scope (`CheckScope::Gate`) on the classes review 1 found no test reaching (the
//! design's "Revision after review 1"): the overloaded symbols of `G`, and definitions without
//! an equation head.

use super::definition;
use crate::{confluence::CheckScope, definition::BackendDefinition, rule::TermIndex};

/// `head(X0) = right` with `X0` bound to `pattern`, of the sorts given, labelled `id`.
fn equation(head: &str, sort: &str, result: &str, pattern: &str, right: &str, id: &str) -> String {
    conditional(head, sort, result, pattern, right, r"\top{R}()", id)
}

/// [`equation`] with the condition `requires`.
fn conditional(
    head: &str,
    sort: &str,
    result: &str,
    pattern: &str,
    right: &str,
    requires: &str,
    id: &str,
) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}({requires}, \and{{R}}(\in{{{sort}, R}}(X0:{sort}, {pattern}), \top{{R}}())),
            \equals{{{result}, R}}({head}{{}}(X0:{sort}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}")]"#
    )
}

fn tainted(definition: &BackendDefinition, symbol: &str) -> bool {
    definition
        .value_claims()
        .tainted_symbols()
        .iter()
        .any(|name| name.as_ref() == symbol)
}

/// V9's comparison of the load's verdict with the full check's, on `definition`.
fn scope_differences(definition: &BackendDefinition) -> Vec<String> {
    let full = definition.value_claims_in_scope(CheckScope::All);
    definition
        .value_claims()
        .claim_differences(&full, definition)
}

/// `gg(z) = fE(e0)` beside `gg(z) = m(z)`, with `fE` over `fN` an overload family of declared
/// functions and, when `heads`, the signature's equation heads.
fn overloaded_function(heads: bool) -> BackendDefinition {
    let declarations = r#"
        symbol fE{}(SortE{}) : SortS{} [function{}()]
        symbol fN{}(SortN{}) : SortS{} [function{}()]
        symbol gg{}(SortNat{}) : SortS{} [function{}()]
        axiom{R} \equals{SortS{}, R}(fE{}(inj{SortN{}, SortE{}}(K0:SortN{})), fN{}(K0:SortN{}))
            [symbol-overload{}(fE{}(), fN{}())]
    "#;
    let axioms = [
        equation(
            "gg",
            "SortNat{}",
            "SortS{}",
            "z{}()",
            "fE{}(e0{}())",
            "to-fe",
        ),
        equation("gg", "SortNat{}", "SortS{}", "z{}()", "m{}(z{}())", "to-m"),
    ];
    let extra = format!("{declarations} {}", axioms.join("\n"));
    if heads {
        definition(&extra)
    } else {
        without_heads(&extra)
    }
}

/// The naturals, `S`, `E` over `N`, and the constructors `z`, `s`, `m`, `n0`, `e0`, with no
/// equation head.
fn without_heads(extra: &str) -> BackendDefinition {
    let source = format!(
        r#"[] module MAIN
            sort SortNat{{}} []
            sort SortS{{}} []
            sort SortE{{}} []
            sort SortN{{}} []
            symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
            axiom{{R}} \exists{{R}}(V:SortE{{}}, \equals{{SortE{{}}, R}}(V:SortE{{}}, inj{{SortN{{}}, SortE{{}}}}(F:SortN{{}}))) [subsort{{SortN{{}}, SortE{{}}}}()]
            symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol m{{}}(SortNat{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol n0{{}}() : SortN{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol e0{{}}() : SortE{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {extra}
        endmodule []"#
    );
    let syntax =
        k_rust_kore::kore::parser::parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// Review 1, F2: the certificate site is asked about an overloaded function, so the load
/// classifies the pair of `gg` that reaches `fE` and withdraws `fE` as the full check does.
#[test]
fn the_load_withdraws_an_overloaded_function_a_pair_reaches() {
    let definition = overloaded_function(true);
    for symbol in ["fE", "fN", "gg"] {
        assert!(tainted(&definition, symbol), "`{symbol}` is withdrawn");
    }
    let fe = TermIndex::Symbol("fE".into());
    assert!(definition.value_claims().admit(&fe).is_none());
    let differences = scope_differences(&definition);
    assert!(differences.is_empty(), "{differences:?}");
}

/// Review 1, F5: without an equation head the check still classifies the pairs that can
/// withdraw a certificate of an overloaded function; it skips stage 2 only when no symbol the
/// gate is asked about can be tainted.
#[test]
fn an_overloaded_function_is_withdrawn_without_an_equation_head() {
    let definition = overloaded_function(false);
    let fe = TermIndex::Symbol("fE".into());
    assert!(
        definition.value_claims().admit(&fe).is_none(),
        "{:?}",
        definition.value_claims().tainted_symbols()
    );
    let differences = scope_differences(&definition);
    assert!(differences.is_empty(), "{differences:?}");
    // Without an overloaded function either, no pair is classified.
    let plain = without_heads(&format!(
        "symbol gg{{}}(SortNat{{}}) : SortS{{}} [function{{}}()] {} {}",
        equation("gg", "SortNat{}", "SortS{}", "z{}()", "m{}(z{}())", "one"),
        equation(
            "gg",
            "SortNat{}",
            "SortS{}",
            "z{}()",
            "m{}(s{}(z{}()))",
            "two"
        ),
    ));
    assert_eq!(plain.value_claims().counts().pairs, 0);
}
