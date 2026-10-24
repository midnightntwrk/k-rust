//! Witness equations (FZ-EMPTYJOIN-WITNESS, design `P7-EMPTYJOIN` 4.1-4.2): a pair over a sort
//! with no normal form whose join reads a stuck partial application as `\bottom` is joined in
//! `M+` through a witness equation that pass 1 proposes and pass 2 validates on `R ∪ W`.

use k_rust_kore::kore::parser::parse_definition;

use crate::{
    confluence::{
        CheckScope, UnjoinedReason, ValueClaims, WitnessPass,
        switches::{self, Switches},
        witness::witness_text,
    },
    definition::BackendDefinition,
};

/// The WASM shape (`#t2aStmt`'s `Defn` and `Instr` equations over the empty `EmptyStmt`):
/// `E < A`, `E < B`, `A < S`, `B < S`, `E` with no symbol; `s(X:A) => da(X)` beside
/// `s(X:B) => ib(X)`; `da(a(I)) => a(0)` and `da(X) => X [owise]`; `ib(b(I)) => b(0)` and no other
/// equation of `ib` (a declared partial function), so `ib(inj{E,B}(Z))` is stuck. The equation
/// head `hd : Int -> A` makes `s`'s equations relevant (T-obs through `X:A`), so the load's scope
/// classifies the pair too (N3).
const SHAPE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortE{} []
    sort SortA{} []
    sort SortB{} []
    sort SortS{} []
    symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
    axiom{R} \exists{R}(V:SortA{}, \equals{SortA{}, R}(V:SortA{}, inj{SortE{}, SortA{}}(F:SortE{}))) [subsort{SortE{}, SortA{}}()]
    axiom{R} \exists{R}(V:SortB{}, \equals{SortB{}, R}(V:SortB{}, inj{SortE{}, SortB{}}(F:SortE{}))) [subsort{SortE{}, SortB{}}()]
    axiom{R} \exists{R}(V:SortS{}, \equals{SortS{}, R}(V:SortS{}, inj{SortA{}, SortS{}}(F:SortA{}))) [subsort{SortA{}, SortS{}}()]
    axiom{R} \exists{R}(V:SortS{}, \equals{SortS{}, R}(V:SortS{}, inj{SortB{}, SortS{}}(F:SortB{}))) [subsort{SortB{}, SortS{}}()]
    symbol a{}(SortInt{}) : SortA{} [constructor{}(), functional{}(), injective{}()]
    symbol b{}(SortInt{}) : SortB{} [constructor{}(), functional{}(), injective{}()]
    symbol s{}(SortS{}) : SortS{} [function{}()]
    symbol da{}(SortA{}) : SortA{} [function{}()]
    symbol ib{}(SortB{}) : SortB{} [function{}()]
    symbol hd{}(SortInt{}) : SortA{} [anywhere{}()]
"#;

/// `head(X0:argument) = right` where `X0` is in `pattern`, labelled `id`, with `attributes`
/// besides its label.
fn equation(
    head: &str,
    argument: &str,
    result: &str,
    pattern: &str,
    right: &str,
    id: &str,
) -> String {
    equation_with(head, argument, result, pattern, right, id, "")
}

fn equation_with(
    head: &str,
    argument: &str,
    result: &str,
    pattern: &str,
    right: &str,
    id: &str,
    attributes: &str,
) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{argument}, R}}(X0:{argument}, {pattern}), \top{{R}}())),
            \equals{{{result}, R}}({head}{{}}(X0:{argument}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}"){attributes}]"#
    )
}

/// The equations of [`SHAPE`].
fn shape_equations() -> Vec<String> {
    let zero = r#"\dv{SortInt{}}("0")"#;
    vec![
        equation(
            "s",
            "SortS{}",
            "SortS{}",
            "inj{SortA{}, SortS{}}(VarX:SortA{})",
            "inj{SortA{}, SortS{}}(da{}(VarX:SortA{}))",
            "sa",
        ),
        equation(
            "s",
            "SortS{}",
            "SortS{}",
            "inj{SortB{}, SortS{}}(VarY:SortB{})",
            "inj{SortB{}, SortS{}}(ib{}(VarY:SortB{}))",
            "sb",
        ),
        equation(
            "da",
            "SortA{}",
            "SortA{}",
            "a{}(VarI:SortInt{})",
            &format!("a{{}}({zero})"),
            "daa",
        ),
        equation_with(
            "da",
            "SortA{}",
            "SortA{}",
            "VarZ:SortA{}",
            "VarZ:SortA{}",
            "daowise",
            ", owise{}()",
        ),
        equation(
            "ib",
            "SortB{}",
            "SortB{}",
            "b{}(VarJ:SortInt{})",
            &format!("b{{}}({zero})"),
            "ibb",
        ),
        equation_with(
            "hd",
            "SortInt{}",
            "SortA{}",
            "VarK:SortInt{}",
            "a{}(VarK:SortInt{})",
            "hda",
            ", anywhere{}()",
        ),
    ]
}

/// The definition of [`SHAPE`], `declarations` and `axioms` at module `MAIN`.
fn load(declarations: &str, axioms: &[String]) -> BackendDefinition {
    let source = format!(
        "[] module MAIN {SHAPE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    super::internalized(&syntax)
}

/// The verdicts of both scopes: the load's and the full check's.
fn both_scopes(definition: &BackendDefinition) -> [(CheckScope, ValueClaims); 2] {
    [
        (CheckScope::Gate, definition.value_claims().clone()),
        (
            CheckScope::All,
            definition.value_claims_in_scope(CheckScope::All),
        ),
    ]
}

fn reasons(claims: &ValueClaims) -> Vec<UnjoinedReason> {
    claims
        .unjoined()
        .iter()
        .map(|pair| pair.reason.clone())
        .collect()
}

/// The witnesses of `claims`, as text.
fn witnesses(claims: &ValueClaims) -> Vec<String> {
    claims
        .witnesses()
        .iter()
        .map(|rule| witness_text(rule))
        .collect()
}

/// The pairs of `claims`, by their equations' ids, sorted.
fn pairs(claims: &ValueClaims) -> Vec<(String, String)> {
    let mut pairs: Vec<_> = claims
        .unjoined()
        .iter()
        .map(|pair| {
            (
                pair.first.attributes.unique_id.clone(),
                pair.second.attributes.unique_id.clone(),
            )
        })
        .collect();
    pairs.sort();
    pairs
}

/// The witness of the WASM shape.
const IB_WITNESS: &str = "ib{}(inj{SortE{}, SortB{}}(VarWitness0:SortE{})) => inj{SortE{}, SortB{}}(VarWitness0:SortE{})";

/// The WASM shape: at the base the pair `sa`/`sb` is listed over `E` in both scopes (the join
/// reads `ib(inj{E,B}(Z))` as `\bottom` and the other side reaches `inj{E,S}(Z)`). With the
/// witness `ib(inj{E,B}(Z)) => inj{E,B}(Z)`, proposed from the open-mode join and validated by
/// pass 2, it joins in both scopes, `ib` stays untainted, and both scopes admit the same claims.
#[test]
fn the_wasm_shape_joins_through_one_witness_in_both_scopes() {
    let definition = load("", &shape_equations());
    for (scope, claims) in both_scopes(&definition) {
        assert_eq!(reasons(&claims), [], "{scope:?}");
        assert!(claims.tainted_symbols().is_empty(), "{scope:?}");
        assert_eq!(witnesses(&claims), [IB_WITNESS], "{scope:?}");
        assert!(claims.witness_pass_adopted(), "{scope:?}");
        let counts = claims.counts();
        assert_eq!(
            (counts.witnesses, counts.witness_pass, counts.equations),
            (1, WitnessPass::Adopted, 6),
            "{scope:?}: {counts:?}"
        );
    }
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(
        definition
            .value_claims()
            .claim_differences(&full, &definition),
        Vec::<String>::new()
    );
}

/// The review's B2 shape: the WASM shape and `m(X:E) => ib(inj X)` beside `m(X:E) => g(X)`, `g`
/// partial with no equation. Pass 1 joins `m` (both sides `\bottom`); the full check's pass 2
/// would not (`inj X` against `\bottom`), so condition 2 keeps pass 1 and `W` empty in both
/// scopes, although the load's scope never classifies `m`'s pair: the decision is the full
/// check's. Both scopes list `sa`/`sb` over `E` and admit the same claims.
#[test]
fn the_b2_shape_keeps_pass_one_in_both_scopes() {
    let mut axioms = shape_equations();
    axioms.push(equation(
        "m",
        "SortE{}",
        "SortB{}",
        "VarW:SortE{}",
        "ib{}(inj{SortE{}, SortB{}}(VarW:SortE{}))",
        "mib",
    ));
    axioms.push(equation(
        "m",
        "SortE{}",
        "SortB{}",
        "VarW:SortE{}",
        "g{}(VarW:SortE{})",
        "mg",
    ));
    let definition = load(
        "symbol m{}(SortE{}) : SortB{} [function{}()] symbol g{}(SortE{}) : SortB{} [function{}()]",
        &axioms,
    );
    for (scope, claims) in both_scopes(&definition) {
        let pairs = claims.unjoined();
        assert_eq!(pairs.len(), 1, "{scope:?}: {:?}", reasons(&claims));
        assert!(pairs[0].over_uninhabited_sort(), "{scope:?}");
        assert_eq!(
            (
                pairs[0].first.attributes.unique_id.as_str(),
                pairs[0].second.attributes.unique_id.as_str()
            ),
            ("sa", "sb"),
            "{scope:?}"
        );
        assert!(claims.witnesses().is_empty(), "{scope:?}");
        assert_eq!(claims.counts().witness_pass, WitnessPass::Kept, "{scope:?}");
    }
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(
        definition
            .value_claims()
            .claim_differences(&full, &definition),
        Vec::<String>::new()
    );
}

/// The test switch `adopt_pass_1` keeps pass 1: the WASM shape's pair is listed over `E` again,
/// as before witnesses (the claims ticket reads this switch).
#[test]
fn adopt_pass_1_keeps_the_pair_over_the_empty_sort() {
    let switches = Switches {
        adopt_pass_1: true,
        ..Switches::default()
    };
    switches::with(switches, || {
        let definition = load("", &shape_equations());
        for (scope, claims) in both_scopes(&definition) {
            assert_eq!(
                reasons(&claims),
                [UnjoinedReason::UninhabitedSort {
                    sort: "SortE".into(),
                    reason: Box::new(UnjoinedReason::DifferentResults),
                }],
                "{scope:?}"
            );
            assert!(claims.witnesses().is_empty(), "{scope:?}");
            assert_eq!(claims.counts().witness_pass, WitnessPass::Kept, "{scope:?}");
        }
    });
}

/// `head(X0:E, X1:A) = right` with `X0 = VarX`, `X1 = VarY`: the variable of `A` makes the
/// equation relevant (T-obs reaches `hd`), so its pairs propose.
fn binary(head: &str, right: &str, id: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortE{{}}, R}}(X0:SortE{{}}, VarX:SortE{{}}), \and{{R}}(\in{{SortA{{}}, R}}(X1:SortA{{}}, VarY:SortA{{}}), \top{{R}}()))),
            \equals{{SortB{{}}, R}}({head}{{}}(X0:SortE{{}}, X1:SortA{{}}), \and{{SortB{{}}}}({right}, \top{{SortB{{}}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}")]"#
    )
}

/// Conflicting proposals (review S1): `k(X:E, Y:A) => f(X)` beside `=> d(X)` proposes
/// `f(X) => d(X)`, `g(X:E, Y:A) => f(X)` beside `=> inj X` proposes `f(X) => inj X`; the two
/// left-hand sides unify and the right-hand sides differ, so both are dropped, no witness is
/// adopted, and both pairs stay listed over `E` in both scopes.
#[test]
fn conflicting_proposals_are_dropped_and_pass_one_is_kept() {
    let symbols = "symbol f{}(SortE{}) : SortB{} [function{}()]
         symbol d{}(SortE{}) : SortB{} [constructor{}(), functional{}(), injective{}()]
         symbol k{}(SortE{}, SortA{}) : SortB{} [function{}()]
         symbol g{}(SortE{}, SortA{}) : SortB{} [function{}()]";
    let k = [
        binary("k", "f{}(VarX:SortE{})", "kf"),
        binary("k", "d{}(VarX:SortE{})", "kd"),
    ];
    // `k`'s pair alone adopts its witness.
    let alone = load(symbols, &k);
    for (scope, claims) in both_scopes(&alone) {
        assert_eq!(pairs(&claims), [], "{scope:?}");
        assert_eq!(
            witnesses(&claims),
            ["f{}(VarWitness0:SortE{}) => d{}(VarWitness0:SortE{})"],
            "{scope:?}"
        );
    }
    let mut axioms = k.to_vec();
    axioms.push(binary("g", "f{}(VarX:SortE{})", "gf"));
    axioms.push(binary("g", "inj{SortE{}, SortB{}}(VarX:SortE{})", "ginj"));
    let definition = load(symbols, &axioms);
    for (scope, claims) in both_scopes(&definition) {
        assert_eq!(
            pairs(&claims),
            [
                ("gf".to_owned(), "ginj".to_owned()),
                ("kf".to_owned(), "kd".to_owned())
            ],
            "{scope:?}"
        );
        assert!(
            claims
                .unjoined()
                .iter()
                .all(|pair| pair.over_uninhabited_sort()),
            "{scope:?}"
        );
        assert!(claims.witnesses().is_empty(), "{scope:?}");
        assert_eq!(claims.counts().witness_pass, WitnessPass::Kept, "{scope:?}");
    }
}

/// Adoption condition 4 (review B1): the WASM shape and an unrelated pair that does not join,
/// `q(I) => ib(b(I))` beside `q(I) => b(1)` (`b(0)` against `b(1)`), which taints `ib`, the
/// witness's head, in the full check's closure. Pass 2 joins `sa`/`sb` and loses nothing, but the
/// witness head is tainted, so pass 1 is kept in both scopes.
#[test]
fn a_tainted_witness_head_keeps_pass_one() {
    let mut axioms = shape_equations();
    axioms.push(equation(
        "q",
        "SortInt{}",
        "SortB{}",
        "VarI:SortInt{}",
        "ib{}(b{}(VarI:SortInt{}))",
        "qib",
    ));
    axioms.push(equation(
        "q",
        "SortInt{}",
        "SortB{}",
        "VarI:SortInt{}",
        r#"b{}(\dv{SortInt{}}("1"))"#,
        "qb",
    ));
    let definition = load("symbol q{}(SortInt{}) : SortB{} [function{}()]", &axioms);
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert!(
        full.tainted_symbols()
            .iter()
            .any(|symbol| symbol.as_ref() == "ib"),
        "{:?}",
        full.tainted_symbols()
    );
    assert_eq!(
        pairs(&full),
        [
            ("qib".to_owned(), "qb".to_owned()),
            ("sa".to_owned(), "sb".to_owned())
        ]
    );
    for (scope, claims) in both_scopes(&definition) {
        assert!(claims.witnesses().is_empty(), "{scope:?}");
        assert_eq!(claims.counts().witness_pass, WitnessPass::Kept, "{scope:?}");
        assert!(
            claims
                .unjoined()
                .iter()
                .any(|pair| pair.over_uninhabited_sort()),
            "{scope:?}: {:?}",
            reasons(&claims)
        );
    }
    assert_eq!(
        definition
            .value_claims()
            .claim_differences(&full, &definition),
        Vec::<String>::new()
    );
}

/// Review S3 (design Q1): only a pair the load's scope classifies proposes. `n(X:E) => ib(inj X)`
/// beside `n(X:E) => inj X`, with no `s` pair and no path from `n` to `hd`: the pair is listed
/// over `E` by the full check, but neither scope proposes (`ib(inj X) => inj X` would join it),
/// so the two scopes read the same model and admit the same claims.
#[test]
fn review_irrelevant_pair_proposes_nothing() {
    let mut axioms = shape_equations()
        .into_iter()
        .filter(|equation| !equation.contains(r#"("sa")"#) && !equation.contains(r#"("sb")"#))
        .collect::<Vec<_>>();
    axioms.push(equation(
        "n",
        "SortE{}",
        "SortB{}",
        "VarW:SortE{}",
        "ib{}(inj{SortE{}, SortB{}}(VarW:SortE{}))",
        "nib",
    ));
    axioms.push(equation(
        "n",
        "SortE{}",
        "SortB{}",
        "VarW:SortE{}",
        "inj{SortE{}, SortB{}}(VarW:SortE{})",
        "ninj",
    ));
    let definition = load("symbol n{}(SortE{}) : SortB{} [function{}()]", &axioms);
    for (scope, claims) in both_scopes(&definition) {
        assert!(claims.witnesses().is_empty(), "{scope:?}");
        assert_eq!(
            claims.counts().witness_pass,
            WitnessPass::NotProposed,
            "{scope:?}"
        );
    }
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(pairs(&full), [("nib".to_owned(), "ninj".to_owned())]);
    assert!(full.unjoined()[0].over_uninhabited_sort());
    assert_eq!(
        definition
            .value_claims()
            .claim_differences(&full, &definition),
        Vec::<String>::new()
    );
}

/// Review S1/S2: the `k`/`g` conflict at `f` beside the WASM shape's good witness at `ib`. The
/// conflicting proposals are dropped, and only they: proposals of different roots never conflict.
/// `W` is the `ib` witness alone, `sa`/`sb` joins, and the `k`/`g` pairs stay listed. Without the
/// conflict rule both `f` witnesses would form an unjoined witness pair and keep pass 1.
#[test]
fn review_conflict_dropped_beside_a_good_witness() {
    let mut axioms = shape_equations();
    axioms.extend([
        binary("k", "f{}(VarX:SortE{})", "kf"),
        binary("k", "d{}(VarX:SortE{})", "kd"),
        binary("g", "f{}(VarX:SortE{})", "gf"),
        binary("g", "inj{SortE{}, SortB{}}(VarX:SortE{})", "ginj"),
    ]);
    let definition = load(
        "symbol f{}(SortE{}) : SortB{} [function{}()]
         symbol d{}(SortE{}) : SortB{} [constructor{}(), functional{}(), injective{}()]
         symbol k{}(SortE{}, SortA{}) : SortB{} [function{}()]
         symbol g{}(SortE{}, SortA{}) : SortB{} [function{}()]",
        &axioms,
    );
    for (scope, claims) in both_scopes(&definition) {
        assert_eq!(witnesses(&claims), [IB_WITNESS], "{scope:?}");
        assert!(claims.witness_pass_adopted(), "{scope:?}");
        assert_eq!(
            pairs(&claims),
            [
                ("gf".to_owned(), "ginj".to_owned()),
                ("kf".to_owned(), "kd".to_owned())
            ],
            "{scope:?}"
        );
    }
}

/// Review B1: the load's scope checks condition 4 on its own second pass. The switch
/// `gate_taints_witnesses` makes that pass taint the witness head, as a witness pair only the
/// load's scope left unjoined would; the full check adopts `W`, the load keeps its pass 1 (the
/// pair listed over `E`, no witness), and the claim comparison (V9) reports the divergence
/// instead of hiding it.
#[test]
fn the_load_keeps_pass_one_when_its_own_second_pass_taints_a_witness_head() {
    let switches = Switches {
        gate_taints_witnesses: true,
        ..Switches::default()
    };
    switches::with(switches, || {
        let definition = load("", &shape_equations());
        let gate = definition.value_claims();
        assert!(gate.witnesses().is_empty());
        assert_eq!(gate.counts().witness_pass, WitnessPass::Kept);
        assert_eq!(
            reasons(gate),
            [UnjoinedReason::UninhabitedSort {
                sort: "SortE".into(),
                reason: Box::new(UnjoinedReason::DifferentResults),
            }]
        );
        assert!(
            !gate
                .tainted_symbols()
                .iter()
                .any(|symbol| symbol.as_ref() == "ib"),
            "{:?}",
            gate.tainted_symbols()
        );
        let full = definition.value_claims_in_scope(CheckScope::All);
        assert_eq!(witnesses(&full), [IB_WITNESS]);
        assert!(
            gate.claim_differences(&full, &definition)
                .iter()
                .any(|difference| difference.starts_with("witness equations")),
            "{:?}",
            gate.claim_differences(&full, &definition)
        );
    });
}

/// The genuine search (`data_term`) with `W` nonempty: beside the WASM shape, whose witness the
/// full check adopts, `t(I) => a(0)` beside `t(I) => a(1)` keeps a ground instance with two normal
/// forms. A witness never applies to a term free of the added constants, so the evaluation the
/// search reads is unchanged.
#[test]
fn a_genuine_pair_stays_genuine_with_a_witness() {
    let mut axioms = shape_equations();
    let zero = r#"a{}(\dv{SortInt{}}("0"))"#;
    let one = r#"a{}(\dv{SortInt{}}("1"))"#;
    axioms.push(equation(
        "t",
        "SortInt{}",
        "SortA{}",
        "VarI:SortInt{}",
        zero,
        "tzero",
    ));
    axioms.push(equation(
        "t",
        "SortInt{}",
        "SortA{}",
        "VarI:SortInt{}",
        one,
        "tone",
    ));
    let definition = load("symbol t{}(SortInt{}) : SortA{} [function{}()]", &axioms);
    let full = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(witnesses(&full), [IB_WITNESS]);
    let heads = definition.data_heads();
    let [finding] = heads.findings() else {
        panic!("one finding: {:?}", heads.findings());
    };
    let instance = finding.instance().expect("a genuine finding");
    let values = [&instance.values.0, &instance.values.1];
    assert_ne!(values[0], values[1], "{instance:?}");
}
