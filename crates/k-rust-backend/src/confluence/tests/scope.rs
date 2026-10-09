//! The load's scope (`CheckScope::Gate`) on the classes review 1 found no test reaching (the
//! design's "Revision after review 1"): pairs at which the relevance filter's decision matters,
//! which need an index that is not a taintable symbol (a hooked root, a collection, a bare
//! variable); the overloaded symbols of `G`; and definitions without an equation head.

use super::definition;
use crate::{
    confluence::{
        CheckScope,
        switches::{self, Switches},
    },
    definition::BackendDefinition,
    rule::TermIndex,
};

/// A hooked function `hf` over `Nat` (its hook never applies to a `Nat`) and a declared
/// function `gl` over lists.
const DECLARATIONS: &str = r#"
    hooked-symbol hf{}(SortNat{}) : SortS{} [function{}(), hook{}("INT.abs")]
    symbol gl{}(SortList{}) : SortS{} [function{}()]
"#;

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

fn load(axioms: &[String]) -> BackendDefinition {
    definition(&format!("{DECLARATIONS} {}", axioms.join("\n")))
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

fn needing_both<R>(run: impl FnOnce() -> R) -> R {
    switches::with(
        Switches {
            relevance_needs_both: true,
            ..Switches::default()
        },
        run,
    )
}

/// An equation of the hooked `listConcat` at `listConcat(L, listUnit)`, a left-hand side the
/// collection's unit law normalizes to the bare variable `L`: indexed at `Variable`, so the
/// check offers it at every position.
fn at_a_variable(requires: &str, id: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}({requires}, \and{{R}}(\in{{SortList{{}}, R}}(X0:SortList{{}}, L:SortList{{}}),
                \and{{R}}(\in{{SortList{{}}, R}}(X1:SortList{{}}, listUnit{{}}()), \top{{R}}()))),
            \equals{{SortList{{}}, R}}(listConcat{{}}(X0:SortList{{}}, X1:SortList{{}}),
                \and{{SortList{{}}}}(listUnit{{}}(), \top{{SortList{{}}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}")]"#
    )
}

/// A condition that mentions the equation head `w`, which makes its equation relevant.
const MENTIONS_W: &str = r"\equals{SortS{}, R}(w{}(z{}()), m{}(z{}()))";

/// The pairs at which exactly one equation is relevant, in both roles: two equations of the
/// hooked `hf` at `z` (only the one reaching `w` relevant; the hook is never tainted, so the
/// two are not linked through their root), in both orders; and an inner pair at a list pattern
/// of the declared function `gl` with an equation indexed at the collection (of the hooked
/// `listItem`) or at a bare variable, each once with the first relevant and once with the
/// second (relevant through a condition that mentions `w`).
fn one_relevant_equation() -> Vec<(&'static str, Vec<String>)> {
    let to_w = equation("hf", "SortNat{}", "SortS{}", "z{}()", "w{}(z{}())", "to-w");
    let to_m = equation("hf", "SortNat{}", "SortS{}", "z{}()", "m{}(z{}())", "to-m");
    let gl = |right: &str, id: &str| {
        equation(
            "gl",
            "SortList{}",
            "SortS{}",
            "listConcat{}(listItem{}(E:SortElement{}), L:SortList{})",
            right,
            id,
        )
    };
    let item = |requires: &str, id: &str| {
        conditional(
            "listItem",
            "SortElement{}",
            "SortList{}",
            "E:SortElement{}",
            "listUnit{}()",
            requires,
            id,
        )
    };
    vec![
        (
            "hooked root, relevant first",
            vec![to_w.clone(), to_m.clone()],
        ),
        ("hooked root, relevant second", vec![to_m, to_w]),
        (
            "collection index, first relevant",
            vec![gl("w{}(z{}())", "gl-w"), item(r"\top{R}()", "item")],
        ),
        (
            "collection index, second relevant",
            vec![gl("m{}(z{}())", "gl-m"), item(MENTIONS_W, "item-w")],
        ),
        (
            "variable index, first relevant",
            vec![
                gl("w{}(z{}())", "gl-w"),
                at_a_variable(r"\top{R}()", "unit"),
            ],
        ),
        (
            "variable index, second relevant",
            vec![
                gl("m{}(z{}())", "gl-m"),
                at_a_variable(MENTIONS_W, "unit-w"),
            ],
        ),
    ]
}

/// Review 1, F1: a non-joined pair with one relevant equation is classified by the load,
/// whichever equation it is, so the load withdraws what the full check withdraws.
#[test]
fn the_load_classifies_a_pair_with_one_relevant_equation_in_either_role() {
    let mut failures = Vec::new();
    for (name, axioms) in one_relevant_equation() {
        let definition = load(&axioms);
        let full = definition.value_claims_in_scope(CheckScope::All);
        if !full.unjoined().iter().any(|pair| pair.relevant()) {
            failures.push(format!(
                "{name}: the full check finds no pair withdrawing a claim"
            ));
        }
        if !tainted(&definition, "w") {
            failures.push(format!("{name}: the load keeps `w`"));
        }
        let differences = scope_differences(&definition);
        if !differences.is_empty() {
            failures.push(format!("{name}: {differences:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// V7 for F1: a filter that classifies a pair only when both equations are relevant skips each
/// of those pairs, and V9's comparison sees it.
#[test]
fn a_filter_needing_both_equations_relevant_is_caught_by_the_scope_comparison() {
    for (name, axioms) in one_relevant_equation() {
        let differences = needing_both(|| scope_differences(&load(&axioms)));
        assert!(
            !differences.is_empty(),
            "{name}: the seeded filter goes unseen"
        );
    }
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
