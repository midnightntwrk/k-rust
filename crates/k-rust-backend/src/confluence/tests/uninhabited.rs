//! Overlaps over a sort with no normal form (FZ-EMPTYSORT; the FZ-DATAEND review's round-4
//! repros `r4-empty` and `r4-partnorule`). Such an overlap has no instance whose arguments are
//! normal forms, but every model
//! of the definition has an element of the sort, at which both equations hold, so the check sets
//! no such overlap aside, under either scope: it is refuted, joined or not joined like any other,
//! and a non-joined one names the sort. It withdraws claims and is reported like any other pair
//! (FZ-EMPTYJOIN-CLAIMS): the claims are read in models with nonempty carriers too.

use k_rust_kore::kore::parser::parse_definition;

use crate::{
    confluence::{
        CheckScope, UnjoinedReason, ValueClaims,
        switches::{self, Switches},
    },
    definition::BackendDefinition,
    term::HeadRole,
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

/// The same pair at an equation head (`h(_:S) => a`, `h(_:S) => bb`, `anywhere`): both scopes
/// classify and list it, naming `S`, and it withdraws `h` and is named at load in both
/// (FZ-EMPTYJOIN-CLAIMS: every model has an element of `S`, at which the pair equates `a` with
/// `bb`, so the claims on `h` rest on no model the pair leaves). Before, it withdrew nothing: the
/// claims were read in `M_NF`, where it has no instance. The scopes admit the same claims.
#[test]
fn a_pair_over_a_sort_with_no_normal_form_withdraws_its_closure_and_is_reported_in_both_scopes() {
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
                pair.relevant() && pair.reported(),
                "{name} {scope:?}: {pair:?}"
            );
            assert_eq!(
                pair.withdrawn
                    .iter()
                    .map(AsRef::as_ref)
                    .collect::<Vec<&str>>(),
                ["h"],
                "{name} {scope:?}"
            );
            assert!(
                claims
                    .tainted_symbols()
                    .iter()
                    .any(|symbol| symbol.as_ref() == "h"),
                "{name} {scope:?}: {:?}",
                claims.tainted_symbols()
            );
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

/// `A, B < T` with two maximal common subsorts: `D` (the constructor `d`) and `empty`, which has
/// no symbol. `h(_:A) => a` beside `h(_:B) => bb` (`anywhere`) has two overlaps, one over each.
fn two_common_subsorts(empty: &str) -> BackendDefinition {
    let subsort = |sub: &str, sup: &str| {
        format!(
            r"axiom{{R}} \exists{{R}}(V:{sup}, \equals{{{sup}, R}}(V:{sup}, inj{{{sub}, {sup}}}(F:{sub}))) [subsort{{{sub}, {sup}}}()]"
        )
    };
    let declarations = [
        "sort SortT{} [] sort SortTA{} [] sort SortTB{} [] sort SortD{} []".to_owned(),
        format!("sort {empty} []"),
        "symbol d{}() : SortD{} [constructor{}(), functional{}(), injective{}()]".to_owned(),
        "symbol h{}(SortT{}) : SortAB{} [anywhere{}()]".to_owned(),
        subsort("SortTA{}", "SortT{}"),
        subsort("SortTB{}", "SortT{}"),
        subsort("SortD{}", "SortTA{}"),
        subsort("SortD{}", "SortTB{}"),
        subsort(empty, "SortTA{}"),
        subsort(empty, "SortTB{}"),
    ]
    .join("\n");
    let equation = |sort: &str, right: &str, id: &str| {
        format!(
            r#"axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortT{{}}, R}}(X0:SortT{{}}, inj{{{sort}, SortT{{}}}}(Var{id}:{sort})), \top{{R}}())),
                \equals{{SortAB{{}}, R}}(h{{}}(X0:SortT{{}}), \and{{SortAB{{}}}}({right}, \top{{SortAB{{}}}}()))
            ) [UNIQUE'Unds'ID{{}}("{id}"), anywhere{{}}()]"#
        )
    };
    load(
        &declarations,
        &[
            equation("SortTA{}", A, "ha"),
            equation("SortTB{}", BB, "hbb"),
        ],
    )
}

/// FZ-EMPTYSORT review B1: a pair with an overlap over an empty sort and one over an inhabited
/// sort (`D`, which evaluation reaches: `h(d)`) is an ordinary pair not joined, which withdraws
/// `h` and is reported, whichever overlap the unifier gives first (the empty sort named before
/// `D` and after it). The branch before the fix stopped at the first non-joined overlap and,
/// when that one was the empty sort's, listed the pair as over it and kept `h`'s claims.
#[test]
fn a_pair_with_a_non_joined_overlap_over_an_inhabited_sort_is_an_ordinary_pair_in_either_order() {
    for empty in ["SortC{}", "SortZ{}"] {
        let definition = two_common_subsorts(empty);
        let full = definition.value_claims_in_scope(CheckScope::All);
        for (scope, claims) in [
            (CheckScope::Gate, definition.value_claims()),
            (CheckScope::All, &full),
        ] {
            assert_eq!(
                reasons(claims),
                [UnjoinedReason::DifferentResults],
                "{empty} {scope:?}"
            );
            let pair = &claims.unjoined()[0];
            assert!(pair.relevant() && pair.reported(), "{empty} {scope:?}");
            assert!(
                claims
                    .tainted_symbols()
                    .iter()
                    .any(|symbol| symbol.as_ref() == "h"),
                "{empty} {scope:?}"
            );
        }
    }
}

/// FZ-EMPTYSORT review S1, repro `inarg`: an inner pair at an argument (`f(h(_:S)) => bb`
/// beside `h(_:S) => a`, `S` empty) over a sort with no normal form is listed and, like every
/// inner pair at an argument whose second equation is an equation head, named at load in both
/// scopes (FZ-EMPTYJOIN-CLAIMS): `fh` is not shown consistent with `ha` at an element of `S`,
/// which every model has. Before, it was not named, the claims being read in `M_NF`.
#[test]
fn an_argument_pair_over_a_sort_with_no_normal_form_is_reported() {
    let definition = load(
        "symbol h{}(SortS{}) : SortAB{} [anywhere{}()] symbol f{}(SortAB{}) : SortAB{} [function{}()]",
        &[
            equation("h", "SortS{}", "SortAB{}", A, "ha", ", anywhere{}()"),
            format!(
                r#"axiom{{R}} \implies{{R}}(
                    \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortAB{{}}, R}}(X0:SortAB{{}}, h{{}}(VarY:SortS{{}})), \top{{R}}())),
                    \equals{{SortAB{{}}, R}}(f{{}}(X0:SortAB{{}}), \and{{SortAB{{}}}}({BB}, \top{{SortAB{{}}}}()))
                ) [UNIQUE'Unds'ID{{}}("fh")]"#
            ),
        ],
    );
    for scope in [CheckScope::Gate, CheckScope::All] {
        let claims = definition.value_claims_in_scope(scope);
        let pairs = claims.unjoined();
        assert_eq!(pairs.len(), 1, "{scope:?}: {:?}", reasons(&claims));
        let pair = &pairs[0];
        assert!(pair.over_uninhabited_sort(), "{scope:?}: {pair:?}");
        assert!(pair.in_argument(), "{scope:?}");
        assert!(pair.reported(), "{scope:?}");
    }
}

/// One scope's load-level counts on WASM: (unjoined pairs, tainted symbols, tainted equation
/// heads, witnesses).
type WasmCounts = (usize, usize, usize, usize);

/// WASM's verdicts under `switches`, the load's then the full check's, and V9's differences.
fn wasm_verdicts(switches: Switches) -> (WasmCounts, WasmCounts, Vec<String>) {
    let path = std::env::var("KRUST_WASM_DEFINITION")
        .expect("KRUST_WASM_DEFINITION names WASM's compiled definition.kore");
    let text = std::fs::read_to_string(&path).expect("the WASM definition is readable");
    // Internalization recurses over the definition's terms: give it the stack WASM needs.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            switches::with(switches, || {
                let syntax = parse_definition(&text).expect("the definition parses");
                let main = syntax.modules.last().expect("a module").name.clone();
                let definition =
                    BackendDefinition::internalize(&syntax, &main).expect("WASM internalizes");
                let heads = definition
                    .symbols()
                    .values()
                    .filter(|symbol| symbol.attributes.head_role() == HeadRole::EquationHead)
                    .map(|symbol| symbol.name.clone())
                    .collect::<Vec<_>>();
                let counts = |claims: &ValueClaims| {
                    let tainted = claims.tainted_symbols();
                    (
                        claims.unjoined().len(),
                        tainted.len(),
                        heads.iter().filter(|head| tainted.contains(head)).count(),
                        claims.witnesses().len(),
                    )
                };
                let full = definition.value_claims_in_scope(CheckScope::All);
                let gate = definition.value_claims();
                (
                    counts(gate),
                    counts(&full),
                    gate.claim_differences(&full, &definition),
                )
            })
        })
        .expect("the loading thread starts")
        .join()
        .expect("loading does not panic")
}

/// WASM (`#t2aStmt`'s `Defn`/`Instr` pair over the empty `EmptyStmt`, design `P7-EMPTYJOIN`
/// section 3). With its witness adopted the load lists no pair and withdraws nothing, and the
/// full check lists 4 pairs and withdraws 8 symbols, as at the witness ticket. With pass 1 forced
/// (`adopt_pass_1`) the pair over `EmptyStmt` now withdraws like any other: 91 symbols (its 6
/// heads) at load, 95 under the full check, as the design's probe measured with such pairs
/// seeding (`KRUST_PROBE_SEED_UNINHABITED`); before FZ-EMPTYJOIN-CLAIMS it withdrew nothing.
/// Both scopes admit the same claims in both runs (V9).
#[test]
#[ignore = "reads WASM's compiled definition.kore named by KRUST_WASM_DEFINITION"]
fn wasm_withdraws_the_empty_sort_pair_only_without_its_witness() {
    let (gate, full, differences) = wasm_verdicts(Switches::default());
    assert_eq!((gate, full), ((0, 0, 0, 1), (4, 8, 0, 1)));
    assert_eq!(differences, Vec::<String>::new());
    let forced = Switches {
        adopt_pass_1: true,
        ..Switches::default()
    };
    let (gate, full, differences) = wasm_verdicts(forced);
    assert_eq!((gate, full), ((1, 91, 6, 0), (5, 95, 6, 0)));
    assert_eq!(differences, Vec::<String>::new());
}
