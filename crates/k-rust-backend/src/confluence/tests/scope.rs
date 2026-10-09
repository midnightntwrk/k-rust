//! The load's scope (`CheckScope::Gate`) on the classes review 1 found no test reaching (the
//! design's "Revision after review 1"): pairs at which the relevance filter's decision matters,
//! which need an index that is not a taintable symbol (a hooked root, a collection, a bare
//! variable); the overloaded symbols of `G`; definitions without an equation head; and the
//! spelling of a reported pair, which must not depend on what the check classified before it.
//! Review 2 added definitions whose only equation head is hooked, which the closure withdraws
//! through a variable's sort (T-obs) or a pin though T-sym never taints a hooked symbol.

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
    // Review 3, R3: the pair withdraws certificates of overloaded functions and no head's
    // claims, and is reported.
    let reported = definition
        .value_claims()
        .unjoined()
        .iter()
        .filter(|pair| pair.relevant())
        .map(|pair| pair.withdrawn.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        reported,
        [vec![
            crate::term::Name::from("fE"),
            crate::term::Name::from("fN")
        ]]
    );
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

/// A hooked `anywhere` symbol `hw : Nat -> S`, an equation head whose hook never applies to a
/// `Nat`, with `extra`, in a signature with no other equation head.
fn hooked_head(extra: &str) -> BackendDefinition {
    without_heads(&format!(
        r#"hooked-symbol hw{{}}(SortNat{{}}) : SortS{{}} [anywhere{{}}(), hook{{}}("INT.abs")]
        {extra}"#
    ))
}

fn assert_withdrawn_alike(definition: &BackendDefinition, symbol: &str) {
    assert!(
        definition
            .value_claims()
            .admit(&TermIndex::Symbol(symbol.into()))
            .is_none(),
        "`{symbol}` is admitted: {:?}",
        definition.value_claims().tainted_symbols()
    );
    let differences = scope_differences(definition);
    assert!(differences.is_empty(), "{differences:?}");
}

/// Review 2, N1 (T-obs): `ff(X) = z` and `ff(X) = s(z)` over `X : S` do not join, and an
/// element of `S` can hold an application of the hooked head `hw`, so the pair withdraws `hw`
/// though it never mentions it. The check must classify the pair although its only equation
/// head is hooked; with an unrelated unhooked head `ww` beside it (no shortcut either way), the
/// closure itself must return `hw`, a symbol T-sym never taints (the debug assertion that the
/// closure returns only `may_be_tainted` symbols reads it).
#[test]
fn a_hooked_equation_head_is_withdrawn_through_a_variable_sort() {
    for unrelated in ["", "symbol ww{}(SortNat{}) : SortNat{} [anywhere{}()]"] {
        let definition = hooked_head(&format!(
            "{unrelated} symbol ff{{}}(SortS{{}}) : SortNat{{}} [function{{}}()] {} {}",
            equation("ff", "SortS{}", "SortNat{}", "X1:SortS{}", "z{}()", "to-z"),
            equation(
                "ff",
                "SortS{}",
                "SortNat{}",
                "X1:SortS{}",
                "s{}(z{}())",
                "to-s"
            ),
        ));
        assert!(tainted(&definition, "hw"), "with `{unrelated}`");
        assert!(!definition.value_claims().unjoined().is_empty());
        assert_withdrawn_alike(&definition, "hw");
    }
}

/// Review 2, N1 (R1.4): a total injective `pin : S -> Int` into the hooked sort `Int` pins the
/// heads an `S` can hold, the hooked `hw` included, with no pair at all.
#[test]
fn a_hooked_equation_head_is_withdrawn_through_a_pin() {
    let definition = hooked_head(
        r#"hooked-sort SortInt{} [hook{}("INT.Int")]
        symbol pin{}(SortS{}) : SortInt{} [function{}(), functional{}(), total{}(), injective{}()]"#,
    );
    assert!(tainted(&definition, "hw"));
    assert_withdrawn_alike(&definition, "hw");
}

/// `w3(X, Y, z) = m(X)` and `w3(z, Y, Z) = m(s(Y))`, which overlap at `w3(z, Y, z)` and do not
/// join, beside `count` non-joined pairs of declared functions `f{i}` at `s(N)`, which withdraw
/// no claim, so that the full check classifies them before (and advances its renaming
/// counters) and the load does not.
fn overlapping_heads(count: usize) -> BackendDefinition {
    let w3 = |patterns: [&str; 3], right: &str, id: &str| {
        let memberships = patterns.iter().enumerate().rev().fold(
            r"\top{R}()".to_owned(),
            |rest, (index, pattern)| {
                format!(
                    r"\and{{R}}(\in{{SortNat{{}}, R}}(X{index}:SortNat{{}}, {pattern}), {rest})"
                )
            },
        );
        format!(
            r#"axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), {memberships}),
                \equals{{SortS{{}}, R}}(
                    w3{{}}(X0:SortNat{{}}, X1:SortNat{{}}, X2:SortNat{{}}),
                    \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}()))
            ) [anywhere{{}}(), UNIQUE'Unds'ID{{}}("{id}")]"#
        )
    };
    let mut extra = format!(
        "symbol w3{{}}(SortNat{{}}, SortNat{{}}, SortNat{{}}) : SortS{{}} [anywhere{{}}()]\n{}\n{}\n",
        w3(
            ["X:SortNat{}", "Y:SortNat{}", "z{}()"],
            "m{}(X:SortNat{})",
            "w3-one"
        ),
        w3(
            ["z{}()", "Y:SortNat{}", "Z:SortNat{}"],
            "m{}(s{}(Y:SortNat{}))",
            "w3-two"
        ),
    );
    for index in 0..count {
        let name = format!("f{index}");
        extra.push_str(&format!(
            "symbol {name}{{}}(SortNat{{}}) : SortNat{{}} [function{{}}()]\n{}\n{}\n",
            equation(
                &name,
                "SortNat{}",
                "SortNat{}",
                "s{}(N:SortNat{})",
                "z{}()",
                &format!("{name}-z")
            ),
            equation(
                &name,
                "SortNat{}",
                "SortNat{}",
                "s{}(N:SortNat{})",
                "s{}(N:SortNat{})",
                &format!("{name}-s")
            ),
        ));
    }
    definition(&extra)
}

/// Review 1, F3 and F4: a reported pair is spelled with the variables the check minted
/// renumbered from 0 in order of first occurrence, so the overlap the warning prints is the same
/// in both scopes and whatever the check classified before the pair.
#[test]
fn a_reported_overlap_is_spelled_alike_in_both_scopes() {
    let overlap = |claims: &crate::confluence::ValueClaims| {
        claims
            .unjoined()
            .iter()
            .filter(|pair| pair.relevant())
            .map(|pair| pair.overlap.clone().expect("a root pair has an overlap"))
            .collect::<Vec<_>>()
    };
    let alone = overlapping_heads(0);
    let expected = overlap(alone.value_claims());
    assert_eq!(expected.len(), 1, "one pair of `w3` withdraws it");
    let minted = expected[0]
        .attributes()
        .variables
        .iter()
        .filter(|variable| variable.name.contains('!'))
        .map(|variable| variable.name.to_string())
        .collect::<Vec<_>>();
    assert!(
        !minted.is_empty() && minted.iter().all(|name| name.ends_with("!apart0")),
        "{expected:?}"
    );
    for count in [1, 12] {
        let definition = overlapping_heads(count);
        let full = definition.value_claims_in_scope(CheckScope::All);
        assert_eq!(full.counts().unjoined, count + 1);
        for claims in [definition.value_claims(), &full] {
            assert_eq!(
                overlap(claims),
                expected,
                "{count} pairs of functions before"
            );
        }
    }
}

/// `wt(inj{A,T}(XA)) = m(z)` and `wt(inj{B,T}(YB)) = m(s(z))`, which overlap only through the
/// common subsorts `C` and `D` of `A` and `B`, at variables the unifier mints, and do not join;
/// with `before`, the declared function `ft` has two equations of the same shape, whose pair
/// withdraws no claim and which the full check classifies before `wt`'s (and advances the
/// unifier's counter) and the load skips.
fn overlapping_through_a_common_subsort(before: bool) -> BackendDefinition {
    let pair = |head: &str, result: &str, rights: [&str; 2]| {
        [("SortA{}", "XA", rights[0]), ("SortB{}", "YB", rights[1])]
            .into_iter()
            .map(|(sort, variable, right)| {
                equation(
                    head,
                    "SortT{}",
                    result,
                    &format!("inj{{{sort}, SortT{{}}}}({variable}:{sort})"),
                    right,
                    &format!("{head}-{variable}"),
                )
            })
            .collect::<Vec<_>>()
    };
    let mut extra = "symbol wt{}(SortT{}) : SortS{} [anywhere{}()]\n".to_owned();
    extra.extend(
        pair("wt", "SortS{}", ["m{}(z{}())", "m{}(s{}(z{}()))"])
            .into_iter()
            .map(|axiom| axiom + "\n"),
    );
    if before {
        extra.push_str("symbol ft{}(SortT{}) : SortNat{} [function{}()]\n");
        extra.extend(
            pair("ft", "SortNat{}", ["z{}()", "s{}(z{}())"])
                .into_iter()
                .map(|axiom| axiom + "\n"),
        );
    }
    definition(&extra)
}

/// Review 3, R1: the variables the unifier mints are spelled with their counter after the
/// marker (`VarOverlap!unify0`), so the canonical spelling of a reported overlap drops the
/// counter that earlier pairs advanced, and the two scopes warn about the same pair alike.
#[test]
fn an_overlap_at_a_variable_the_unifier_mints_is_spelled_alike_in_both_scopes() {
    let overlaps = |claims: &crate::confluence::ValueClaims| {
        claims
            .unjoined()
            .iter()
            .filter(|pair| pair.relevant())
            .map(|pair| pair.overlap.clone().expect("a root pair has an overlap"))
            .collect::<Vec<_>>()
    };
    let alone = overlapping_through_a_common_subsort(false);
    let expected = overlaps(alone.value_claims());
    assert!(!expected.is_empty(), "the pairs of `wt` withdraw it");
    let minted = expected
        .iter()
        .flat_map(|overlap| overlap.attributes().variables.iter())
        .map(|variable| variable.name.to_string())
        .collect::<Vec<_>>();
    assert!(
        minted
            .iter()
            .any(|name| name.starts_with("VarOverlap!unify")),
        "{expected:?}"
    );
    let definition = overlapping_through_a_common_subsort(true);
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert!(
        full.counts().unjoined > definition.value_claims().counts().unjoined,
        "the full check classifies `ft`'s pair as well"
    );
    assert!(tainted(&definition, "wt") && !tainted(&definition, "ft"));
    for claims in [definition.value_claims(), &full] {
        assert_eq!(overlaps(claims), expected);
    }
    assert_eq!(scope_differences(&definition), Vec::<String>::new());
}
