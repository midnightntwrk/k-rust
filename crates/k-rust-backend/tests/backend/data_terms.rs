//! Data terms (`k_rust_backend::data_term`): which ground terms are data, and which overload
//! heads two definitions agree on. The fixture is FUN's overloaded list family
//! (`tests/fixtures/overloaded-list-owise.kore`): `exps`, `vals` and `listExp` root only overload
//! equations, `pipe` is an `anywhere` head with no equation, `ordinaryVals` a declared function.

use k_rust_backend::{
    data_term::{DataHeads, Stuck},
    definition::BackendDefinition,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

const FIXTURE: &str = include_str!("../fixtures/overloaded-list-owise.kore");

fn definition(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("fixture should parse");
    BackendDefinition::internalize(&syntax, "OVERLOADED-LIST-OWISE")
        .expect("fixture should internalize")
}

/// The fixture with `extra` sentences added to its module.
fn with_sentences(extra: &str) -> BackendDefinition {
    let (head, tail) = FIXTURE
        .rsplit_once("endmodule")
        .expect("the fixture has one module");
    definition(&format!("{head}\n{extra}\nendmodule{tail}"))
}

/// The fixture without the sentence that contains `marker`.
fn without_sentence(marker: &str) -> BackendDefinition {
    let start = FIXTURE.find(marker).expect("marker in fixture");
    let begin = FIXTURE[..start]
        .rfind("axiom")
        .expect("an axiom before the marker");
    let end = start
        + FIXTURE[start..]
            .find("]\n")
            .expect("the axiom's attributes end")
        + 2;
    definition(&format!("{}{}", &FIXTURE[..begin], &FIXTURE[end..]))
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .admit_unverified(&syntax, &[])
        .internalize_term()
        .expect("term should internalize")
}

fn data(definition: &BackendDefinition, heads: &DataHeads, source: &str) -> bool {
    definition.is_data(&term(definition, source), heads)
}

fn names(heads: &DataHeads) -> Vec<String> {
    heads.names().map(ToString::to_string).collect()
}

const EMPTY_EXPS: &str = "inj{SortBottoms{}, SortExps{}}(dotBottoms{}())";
const EMPTY_VALS: &str = "inj{SortBottoms{}, SortVals{}}(dotBottoms{}())";
/// `fun, .Exps`: `fun` is an `Exp` that is no `Val` and no `Bottom`, so no overload equation of
/// `exps` applies.
const FUN_EXPS: &str = "exps{}(fun{}(), inj{SortBottoms{}, SortExps{}}(dotBottoms{}()))";
/// `one, .Exps`: `one` is a `Val`, so the overload equation to `vals` applies.
const ONE_EXPS: &str =
    "exps{}(inj{SortVal{}, SortExp{}}(one{}()), inj{SortBottoms{}, SortExps{}}(dotBottoms{}()))";

#[test]
fn the_overload_only_heads_are_the_data_heads() {
    let definition = definition(FIXTURE);
    // `pipe` roots no equation, `ordinaryVals` is a declared function, the rest are constructors
    // or functions; the nullary heads are heads, whose applications every equation reaches.
    assert_eq!(
        names(&definition.data_heads()),
        ["dotExps", "dotVals", "exps", "listExp", "vals"]
    );
}

#[test]
fn an_irreducible_overload_application_over_data_is_data() {
    let definition = definition(FIXTURE);
    let heads = definition.data_heads();
    assert!(data(&definition, &heads, FUN_EXPS));
    assert!(data(
        &definition,
        &heads,
        &format!("vals{{}}(one{{}}(), {EMPTY_VALS})")
    ));
    // Nested: `[fun, .Exps]` as an `Exp`, inside a constructor.
    assert!(data(
        &definition,
        &heads,
        &format!("exps{{}}(listExp{{}}({FUN_EXPS}), {EMPTY_EXPS})")
    ));
    // The constructor-like terms stay data whatever the heads.
    assert!(data(&definition, &DataHeads::default(), EMPTY_EXPS));
}

#[test]
fn an_application_an_overload_equation_reaches_is_not_data() {
    let definition = definition(FIXTURE);
    let heads = definition.data_heads();
    assert!(!data(&definition, &heads, ONE_EXPS));
    // Below a data constructor too, and for a nullary head, which its equation always reaches.
    assert!(!data(
        &definition,
        &heads,
        &format!(
            "listVal{{}}(vals{{}}(inj{{SortBottom{{}}, SortVal{{}}}}(bottom{{}}()), {EMPTY_VALS}))"
        )
    ));
    assert!(!data(&definition, &heads, "dotExps{}()"));
}

#[test]
fn function_applications_and_heads_with_no_equation_are_not_data() {
    let definition = definition(FIXTURE);
    let heads = definition.data_heads();
    assert!(!data(
        &definition,
        &heads,
        &format!("ordinaryVals{{}}({EMPTY_VALS})")
    ));
    assert!(!data(
        &definition,
        &heads,
        &format!(
            "exps{{}}(fun{{}}(), inj{{SortVals{{}}, SortExps{{}}}}(ordinaryVals{{}}({EMPTY_VALS})))"
        )
    ));
    assert!(!data(
        &definition,
        &heads,
        &format!("pipe{{}}({FUN_EXPS}, fun{{}}())")
    ));
    assert!(!data(
        &definition,
        &heads,
        "getMatching{}(fun{}(), one{}())"
    ));
}

#[test]
fn a_head_outside_the_given_heads_is_not_data() {
    let definition = definition(FIXTURE);
    assert!(!data(&definition, &DataHeads::default(), FUN_EXPS));
}

/// `pick(exps(E, Es)) = one` and `pick(inj(vals(V, Vs))) = inj(bottom)` overlap at
/// `pick(exps(inj(K0), inj(K1)))`, which the overload equation lowers to the second left-hand
/// side: the reducts `one` and `inj(bottom)` do not join. The definition then equates values
/// the normal forms keep apart, the check taints both equations' heads, and no application of
/// `exps` or `vals` is data.
#[test]
fn an_unjoined_critical_pair_withdraws_the_head() {
    let definition = with_sentences(
        r#"
    symbol pick{}(SortExps{}) : SortVal{} [function{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExps{}, R}(X0:SortExps{}, exps{}(E:SortExp{}, Es:SortExps{})), \top{R}())),
        \equals{SortVal{}, R}(pick{}(X0:SortExps{}), \and{SortVal{}}(one{}(), \top{SortVal{}}())))
        [label{}("pick-exps")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExps{}, R}(X0:SortExps{}, inj{SortVals{}, SortExps{}}(vals{}(V:SortVal{}, Vs:SortVals{}))), \top{R}())),
        \equals{SortVal{}, R}(pick{}(X0:SortExps{}), \and{SortVal{}}(inj{SortBottom{}, SortVal{}}(bottom{}()), \top{SortVal{}}())))
        [label{}("pick-vals")]
"#,
    );
    let tainted = definition.value_claims().tainted_symbols();
    assert!(
        tainted.iter().any(|name| name.as_ref() == "exps"),
        "{tainted:?}"
    );
    let heads = definition.data_heads();
    assert!(!heads.names().any(|name| name.as_ref() == "exps"));
    assert!(!data(&definition, &heads, FUN_EXPS));
    // The definition is not shown confluent, so no term is data (FZ-DATAEND review round 3: an
    // identification reaches other terms through every equation that tells them apart), not
    // even a constructor term the pair does not mention; the finding names the pair.
    assert!(!heads.confluent());
    assert!(
        heads.findings().iter().any(|finding| {
            let text = finding.to_string();
            text.contains("pick-exps") && text.contains("pick-vals")
        }),
        "{:?}",
        heads.findings()
    );
    assert!(!data(&definition, &heads, "fun{}()"));
    assert!(!data(&definition, &heads, "state{}(matchFailure{}())"));
}

/// An overload equation whose argument is not a variable or an injection of one (here the
/// constant `one`, as an overload placed across `K` has `kseq(inj(X), dotk)`, FZ-DATAEND review
/// B1) is outside the argument: whether it applies reads more than injection sorts. Its head is
/// not a data head.
#[test]
fn a_head_with_an_overload_equation_of_another_shape_is_not_a_data_head() {
    let definition = with_sentences(
        r#"
    axiom{} \equals{SortExps{}, SortExps{}}(
        exps{}(inj{SortVal{}, SortExp{}}(one{}()), inj{SortVals{}, SortExps{}}(K1:SortVals{})),
        inj{SortVals{}, SortExps{}}(vals{}(one{}(), K1:SortVals{})))
        [symbol-overload{}(exps{}(), vals{}())]
"#,
    );
    let heads = definition.data_heads();
    assert!(!heads.names().any(|name| name.as_ref() == "exps"));
    assert!(!data(&definition, &heads, FUN_EXPS));
    // The load only reports the shape (`ViolationKind::OverloadShape`); the family's lowering is
    // then outside the check's premises, so the definition has no data.
    assert!(
        definition
            .value_claims()
            .violations()
            .iter()
            .any(|violation| !violation.kind.withdraws())
    );
    assert!(!heads.confluent());
    assert!(!data(&definition, &heads, "fun{}()"));
}

/// Two total-function equations at one root with different results (`q(X) = one`, `q(X) =
/// inj(bottom)`) equate `one` with `inj{Bottom,Val}(bottom)`: no injection axiom keeps them
/// apart. The full check finds the pair (the load's check pairs it only where it can withdraw a
/// value claim; `r3-plainq` in the fuzz tests is a definition where it does not), so the
/// definition has no data (FZ-DATAEND review round 3, R3-S1).
#[test]
fn a_pair_of_function_equations_with_different_results_withdraws_all_data() {
    let definition = with_sentences(
        r#"
    symbol q{}(SortVal{}) : SortVal{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, V:SortVal{}), \top{R}())),
        \equals{SortVal{}, R}(q{}(X0:SortVal{}), \and{SortVal{}}(one{}(), \top{SortVal{}}())))
        [label{}("q-one")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, V:SortVal{}), \top{R}())),
        \equals{SortVal{}, R}(q{}(X0:SortVal{}), \and{SortVal{}}(inj{SortBottom{}, SortVal{}}(bottom{}()), \top{SortVal{}}())))
        [label{}("q-bottom")]
"#,
    );
    let heads = definition.data_heads();
    assert!(!heads.confluent(), "{:?}", heads.findings());
    assert!(!data(&definition, &heads, "one{}()"));
    // The finding is genuine (FZ-POLISH review round 3): at `q(one)` both equations apply and
    // the input has two normal forms, `one` and `inj{Bottom,Val}(bottom)`.
    let [finding] = heads.findings() else {
        panic!("one finding: {:?}", heads.findings());
    };
    let instance = finding.instance().expect("a genuine finding");
    assert_eq!(
        instance.overlap,
        term(&definition, "q{}(one{}())"),
        "{instance:?}"
    );
    let values = [&instance.values.0, &instance.values.1];
    assert!(
        values.contains(&&term(&definition, "one{}()")),
        "{values:?}"
    );
    assert!(
        values.contains(&&term(
            &definition,
            "inj{SortBottom{}, SortVal{}}(bottom{}())"
        )),
        "{values:?}"
    );
    // Assumed joined, the pair no longer withdraws every datum: the definition has data again.
    let assumed = definition.data_heads_assuming(&heads, |_| true);
    assert!(assumed.confluent(), "{:?}", assumed.findings());
    assert_eq!(assumed.assumed().len(), 1);
    assert!(data(&definition, &assumed, "one{}()"));
    // Nothing assumed, nothing changes.
    assert!(
        !definition
            .data_heads_assuming(&heads, |_| false)
            .confluent()
    );
}

/// FZ-POLISH: two equations whose results are distinct constructors of one sort at a ground
/// instance make the finding genuine: at `s(one)` both apply, and the input has the two normal
/// forms `failed` and `bound(one)`.
#[test]
fn a_pair_equating_two_constructors_of_one_sort_is_genuine() {
    let definition = with_sentences(
        r#"
    symbol s{}(SortVal{}) : SortState{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, V:SortVal{}), \top{R}())),
        \equals{SortState{}, R}(s{}(X0:SortVal{}), \and{SortState{}}(failed{}(), \top{SortState{}}())))
        [label{}("s-failed")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, V:SortVal{}), \top{R}())),
        \equals{SortState{}, R}(s{}(X0:SortVal{}), \and{SortState{}}(bound{}(V:SortVal{}), \top{SortState{}}())))
        [label{}("s-bound")]
"#,
    );
    let heads = definition.data_heads();
    let [finding] = heads.findings() else {
        panic!("one finding: {:?}", heads.findings());
    };
    let instance = finding.instance().expect("a genuine finding");
    assert_eq!(
        instance.overlap,
        term(&definition, "s{}(one{}())"),
        "{instance:?}"
    );
    let values = [&instance.values.0, &instance.values.1];
    assert!(
        values.contains(&&term(&definition, "failed{}()")),
        "{values:?}"
    );
    assert!(
        values.contains(&&term(&definition, "bound{}(one{}())")),
        "{values:?}"
    );
}

/// A pair whose conditions no small ground instance makes true stays undecided (FZ-POLISH):
/// `r(V) = one requires stuck(V)` beside `r(V) = inj(bottom)`, where the function `stuck` has no
/// equation, so its application never evaluates to `true`. The check cannot refute the
/// conditions either, so it reports the pair as not shown to join, never as genuine.
#[test]
fn a_pair_whose_conditions_hold_on_no_tried_instance_is_undecided() {
    let definition = with_sentences(
        r#"
    symbol r{}(SortVal{}) : SortVal{} [function{}(), total{}()]
    symbol stuck{}(SortVal{}) : SortBool{} [function{}()]
    axiom{R} \implies{R}(
        \and{R}(\equals{SortBool{}, R}(stuck{}(V:SortVal{}), \dv{SortBool{}}("true")),
            \and{R}(\in{SortVal{}, R}(X0:SortVal{}, V:SortVal{}), \top{R}())),
        \equals{SortVal{}, R}(r{}(X0:SortVal{}), \and{SortVal{}}(one{}(), \top{SortVal{}}())))
        [label{}("r-one")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, V:SortVal{}), \top{R}())),
        \equals{SortVal{}, R}(r{}(X0:SortVal{}), \and{SortVal{}}(inj{SortBottom{}, SortVal{}}(bottom{}()), \top{SortVal{}}())))
        [label{}("r-bottom")]
"#,
    );
    let heads = definition.data_heads();
    let pairs = heads
        .findings()
        .iter()
        .filter(|finding| finding.to_string().contains("r-one"))
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 1, "{:?}", heads.findings());
    let pair = pairs[0].pair().expect("a pair finding");
    assert_eq!(
        pair.reason,
        k_rust_backend::confluence::UnjoinedReason::ConditionOpen
    );
    assert!(pair.conditions.is_some(), "{pair:?}");
    assert!(!pairs[0].is_genuine(), "{:?}", pairs[0].instance());
}

#[test]
fn a_head_with_another_equation_or_a_lemma_is_not_a_data_head() {
    let anywhere = with_sentences(
        r#"
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExp{}, R}(X0:SortExp{}, fun{}()),
            \and{R}(\in{SortExps{}, R}(X1:SortExps{}, Es:SortExps{}), \top{R}()))),
        \equals{SortExps{}, R}(exps{}(X0:SortExp{}, X1:SortExps{}), \and{SortExps{}}(Es:SortExps{}, \top{SortExps{}}())))
        [label{}("drop-fun"), anywhere{}()]
"#,
    );
    assert!(
        !anywhere
            .data_heads()
            .names()
            .any(|name| name.as_ref() == "exps")
    );
    let lemma = with_sentences(
        r#"
    axiom{R} \implies{R}(
        \top{R}(),
        \equals{SortVals{}, R}(vals{}(one{}(), Vs:SortVals{}), \and{SortVals{}}(Vs:SortVals{}, \top{SortVals{}}())))
        [label{}("lemma"), simplification{}()]
"#,
    );
    assert!(
        !lemma
            .data_heads()
            .names()
            .any(|name| name.as_ref() == "vals")
    );
}

/// A term is judged by each definition with its own facts (FZ-DATAEND review round 2): a sort
/// `Zero` that is below `Val` in one definition and only below `Exp` in the other makes
/// `exps(inj{Zero,Exp}(zero), .Exps)` reducible in the first (the overload equation to `vals`
/// matches through the subsort) and a normal form in the second. A comparison of ends across the
/// two must refuse it: it is data in one definition only.
#[test]
fn each_definition_judges_a_term_by_its_own_subsorts() {
    let zero = |below: &str| {
        with_sentences(&format!(
            r#"
    sort SortZero{{}} []
    symbol zero{{}}() : SortZero{{}} [constructor{{}}()]
    axiom{{R}} \exists{{R}}(V:Sort{below}{{}}, \equals{{Sort{below}{{}}, R}}(V:Sort{below}{{}}, inj{{SortZero{{}}, Sort{below}{{}}}}(F:SortZero{{}})))
        [subsort{{SortZero{{}}, Sort{below}{{}}}}()]
    axiom{{R}} \exists{{R}}(V:SortExp{{}}, \equals{{SortExp{{}}, R}}(V:SortExp{{}}, inj{{SortZero{{}}, SortExp{{}}}}(F:SortZero{{}})))
        [subsort{{SortZero{{}}, SortExp{{}}}}()]
"#
        ))
    };
    let below_val = zero("Val");
    let only_exp = zero("Name");
    let subject = format!("exps{{}}(inj{{SortZero{{}}, SortExp{{}}}}(zero{{}}()), {EMPTY_EXPS})");
    assert!(!data(&below_val, &below_val.data_heads(), &subject));
    assert!(data(&only_exp, &only_exp.data_heads(), &subject));
    // The heads themselves are the same in both: only the judgement of the term differs.
    assert_eq!(
        names(&below_val.data_heads()),
        names(&only_exp.data_heads())
    );
}

/// The two definitions give `exps` different equations (one lacks the lowering to `vals`), and
/// `one, .Exps` is a normal form of the second only.
#[test]
fn each_definition_judges_a_term_by_its_own_equations() {
    let baseline = definition(FIXTURE);
    let unlowered = without_sentence("symbol-overload{}(listExp{}(), listVal{}())");
    let list = format!(
        "listExp{{}}(inj{{SortVals{{}}, SortExps{{}}}}(vals{{}}(one{{}}(), {EMPTY_VALS})))"
    );
    assert!(!data(&baseline, &baseline.data_heads(), &list));
    // Without its overload equation `listExp` roots no equation: not a data head either.
    assert!(!data(&unlowered, &unlowered.data_heads(), &list));
    assert!(data(&baseline, &baseline.data_heads(), FUN_EXPS));
    assert!(data(&unlowered, &unlowered.data_heads(), FUN_EXPS));
}

/// INT8 follow-ups (review N4): an equation whose right-hand side has a variable its left-hand
/// side does not bind (`any(X0) = Y`) is a decided finding: read as written it equates `any(X0)`
/// with every `Val`, and the evaluator never applies it. Only hand-written KORE gives one (k-rust
/// refuses `Y` in K source). It keeps the definition without data, and no assumption moves it.
#[test]
fn an_equation_with_an_unbound_result_variable_is_decided_and_never_assumed() {
    let definition = with_sentences(
        r#"
    symbol any{}(SortExps{}) : SortVal{} [function{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExps{}, R}(X0:SortExps{}, Es:SortExps{}), \top{R}())),
        \equals{SortVal{}, R}(any{}(X0:SortExps{}), \and{SortVal{}}(Y:SortVal{}, \top{SortVal{}}())))
        [label{}("any-unbound")]
"#,
    );
    let heads = definition.data_heads();
    let decided = heads
        .findings()
        .iter()
        .filter(|finding| finding.is_decided())
        .collect::<Vec<_>>();
    assert_eq!(decided.len(), 1, "{:?}", heads.findings());
    assert!(
        matches!(decided[0], k_rust_backend::data_term::Finding::Equation(pair)
            if pair.reason == k_rust_backend::confluence::UnjoinedReason::UnboundResultVariables),
        "{:?}",
        decided[0]
    );
    let assumed = definition.data_heads_assuming(&heads, |_| true);
    assert!(!assumed.confluent());
    assert!(
        assumed
            .findings()
            .iter()
            .any(|finding| finding.is_decided())
    );
    assert!(
        assumed
            .assumed()
            .iter()
            .all(|finding| !finding.is_decided())
    );
}

/// INT8 follow-ups review round 2 (R2-B1): a `PinnedByInjectiveTotal` row also withdraws claims,
/// but it names no equation: it is an overload premise, not a decided fact about an equation's
/// left-hand side, so it is not decided (and can be assumed), unlike the three rows about an
/// executable equation's left-hand side.
#[test]
fn a_pinned_injective_row_is_not_decided() {
    use k_rust_backend::{
        confluence::{Violation, ViolationKind},
        data_term::Finding,
        rule::TermIndex,
    };
    let row = |kind| Finding::Precondition(Violation { rule: None, kind });
    assert!(!row(ViolationKind::PinnedByInjectiveTotal("Lblenc".into())).is_decided());
    assert!(!row(ViolationKind::OverloadShape("Lblf".into())).is_decided());
    assert!(row(ViolationKind::ConstructorHeaded("Lblc".into())).is_decided());
    assert!(row(ViolationKind::InjectionHeaded).is_decided());
    assert!(row(ViolationKind::IndexedAt(TermIndex::List)).is_decided());
}

/// One equation `HEAD(X0) = RHS requires REQUIRES` of the fixture's shape, `X0` bound to `V`.
fn equation(head: &str, sort: &str, rhs: &str, requires: &str, label: &str) -> String {
    attributed_equation(
        head,
        sort,
        rhs,
        requires,
        &format!(r#"label{{}}("{label}")"#),
    )
}

/// [`equation`] with the attribute list `attributes`.
fn attributed_equation(
    head: &str,
    sort: &str,
    rhs: &str,
    requires: &str,
    attributes: &str,
) -> String {
    format!(
        r#"
    axiom{{R}} \implies{{R}}(
        \and{{R}}({requires}, \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, V:SortVal{{}}), \top{{R}}())),
        \equals{{{sort}, R}}({head}{{}}(X0:SortVal{{}}), \and{{{sort}}}({rhs}, \top{{{sort}}}())))
        [{attributes}]
"#
    )
}

/// `cap(listVal(Vs)) = one`: a declared total function that no equation rewrites at `one`.
const CAP: &str = r#"
    symbol cap{}(SortVal{}) : SortVal{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, listVal{}(Vs:SortVals{})), \top{R}())),
        \equals{SortVal{}, R}(cap{}(X0:SortVal{}), \and{SortVal{}}(one{}(), \top{SortVal{}}())))
        [label{}("cap-list")]
"#;

/// `nb`: a declared partial function without an equation.
const NB: &str = "    symbol nb{}(SortVal{}) : SortVal{} [function{}()]";

/// The one pair finding whose description names `label`.
fn pair_finding<'h>(heads: &'h DataHeads, label: &str) -> &'h k_rust_backend::data_term::Finding {
    let found = heads
        .findings()
        .iter()
        .filter(|finding| finding.pair().is_some() && finding.to_string().contains(label))
        .collect::<Vec<_>>();
    let [finding] = found[..] else {
        panic!("one pair finding naming {label}: {:?}", heads.findings());
    };
    finding
}

/// S2B-T3 (KEVM `Cgascap`'s shape): `p(V) = one` beside `p(V) = cap(V)`, where `cap` is a
/// declared total function whose only equation does not match `one`. At `p(one)` both apply, and
/// the reducts are the two normal forms `one` and the stuck total application `cap(one)`.
#[test]
fn a_stuck_total_application_against_a_constructor_is_genuine() {
    let definition = with_sentences(&format!(
        "{CAP}\n    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation("p", "SortVal{}", "one{}()", r"\top{R}()", "p-one"),
        equation(
            "p",
            "SortVal{}",
            "cap{}(V:SortVal{})",
            r"\top{R}()",
            "p-cap"
        ),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "p-one");
    let instance = finding.instance().expect("a genuine finding");
    assert_eq!(
        instance.overlap,
        term(&definition, "p{}(one{}())"),
        "{instance:?}"
    );
    let values = [&instance.values.0, &instance.values.1];
    assert!(
        values.contains(&&term(&definition, "one{}()")),
        "{values:?}"
    );
    assert!(
        values.contains(&&term(&definition, "cap{}(one{}())")),
        "{values:?}"
    );
}

/// S2B-T3 (KEVM's Merkle splitter's shape): `s(V) = failed` beside `s(V) = bound(nb(V))`, where
/// `nb` is a declared partial function without an equation. At `s(one)` one reduct is the
/// normal form `failed` and the other holds the stuck partial application `nb(one)` under a
/// constructor, `\bottom` in `M_NF`.
#[test]
fn a_stuck_partial_application_under_a_constructor_against_a_constructor_is_genuine() {
    let definition = with_sentences(&format!(
        "{NB}\n    symbol s{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation("s", "SortState{}", "failed{}()", r"\top{R}()", "s-failed"),
        equation(
            "s",
            "SortState{}",
            "bound{}(nb{}(V:SortVal{}))",
            r"\top{R}()",
            "s-nb"
        ),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "s-failed");
    let instance = finding.instance().expect("a genuine finding");
    assert_eq!(
        instance.overlap,
        term(&definition, "s{}(one{}())"),
        "{instance:?}"
    );
    let values = [&instance.values.0, &instance.values.1];
    assert!(
        values.contains(&&term(&definition, "failed{}()")),
        "{values:?}"
    );
    assert!(
        values.contains(&&term(&definition, "bound{}(nb{}(one{}()))")),
        "{values:?}"
    );
}

/// S2B-T3: two reducts that are both undefined at every tried instance are no instance:
/// `f(V) = g(V)` beside `f(V) = h(V)`, with `g` and `h` declared partial functions whose only
/// equations match `listVal(_)` and agree there.
#[test]
fn two_stuck_partial_reducts_stay_undecided() {
    let definition = with_sentences(&format!(
        r#"
    symbol g{{}}(SortVal{{}}) : SortVal{{}} [function{{}}()]
    symbol h{{}}(SortVal{{}}) : SortVal{{}} [function{{}}()]
    symbol f{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, listVal{{}}(Vs:SortVals{{}})), \top{{R}}())),
        \equals{{SortVal{{}}, R}}(g{{}}(X0:SortVal{{}}), \and{{SortVal{{}}}}(one{{}}(), \top{{SortVal{{}}}}())))
        [label{{}}("g-list")]
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, listVal{{}}(Vs:SortVals{{}})), \top{{R}}())),
        \equals{{SortVal{{}}, R}}(h{{}}(X0:SortVal{{}}), \and{{SortVal{{}}}}(one{{}}(), \top{{SortVal{{}}}}())))
        [label{{}}("h-list")]
{}{}"#,
        equation("f", "SortVal{}", "g{}(V:SortVal{})", r"\top{R}()", "f-g"),
        equation("f", "SortVal{}", "h{}(V:SortVal{})", r"\top{R}()", "f-h"),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "f-g");
    assert!(!finding.is_genuine(), "{:?}", finding.instance());
}

/// S2B-T3 (review S6): a stuck application of a total function with an algebraic axiom is no
/// value: `cat` is `assoc`, whose emitted axiom equates the two reducts of `f(V) = cat(cat(V, V),
/// V)` beside `f(V) = cat(V, cat(V, V))`, so the pair stays undecided.
#[test]
fn a_stuck_application_of_an_associative_total_function_stays_undecided() {
    let definition = with_sentences(&format!(
        "    symbol cat{{}}(SortVal{{}}, SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}(), assoc{{}}()]
    symbol f{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation(
            "f",
            "SortVal{}",
            "cat{}(cat{}(V:SortVal{}, V:SortVal{}), V:SortVal{})",
            r"\top{R}()",
            "f-left"
        ),
        equation(
            "f",
            "SortVal{}",
            "cat{}(V:SortVal{}, cat{}(V:SortVal{}, V:SortVal{}))",
            r"\top{R}()",
            "f-right"
        ),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "f-left");
    assert!(!finding.is_genuine(), "{:?}", finding.instance());
}

/// S2B-T3 (review N6): a stuck partial application under a stuck total application, or under a
/// hooked symbol, is neither defined nor undefined, and gives no instance: `s(V) = failed`
/// beside `s(V) = state(tot(nb(V)))` (`tot` total and `nb` partial, neither with an equation),
/// and `b(V) = failed` beside `b(V) = flag(notBool(brb(V)))` (`brb` partial without an equation).
/// A hooked application is no value even over a defined argument: `t(V) = failed` beside
/// `t(V) = flag(notBool(tb(V)))` (`tb` total without an equation) stays undecided too.
#[test]
fn a_stuck_partial_application_under_a_stuck_total_or_hooked_symbol_gives_no_instance() {
    let definition = with_sentences(&format!(
        r#"
    symbol tot{{}}(SortVal{{}}) : SortMatchResult{{}} [function{{}}(), total{{}}()]
{NB}
    symbol brb{{}}(SortVal{{}}) : SortBool{{}} [function{{}}()]
    symbol tb{{}}(SortVal{{}}) : SortBool{{}} [function{{}}(), total{{}}()]
    hooked-symbol notBool{{}}(SortBool{{}}) : SortBool{{}} [function{{}}(), functional{{}}(), total{{}}(), hook{{}}("BOOL.not")]
    symbol flag{{}}(SortBool{{}}) : SortState{{}} [constructor{{}}()]
    symbol s{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]
    symbol b{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]
    symbol t{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]
{}{}{}{}{}{}"#,
        equation("s", "SortState{}", "failed{}()", r"\top{R}()", "s-failed"),
        equation(
            "s",
            "SortState{}",
            "state{}(tot{}(nb{}(V:SortVal{})))",
            r"\top{R}()",
            "s-tot"
        ),
        equation("b", "SortState{}", "failed{}()", r"\top{R}()", "b-failed"),
        equation(
            "b",
            "SortState{}",
            "flag{}(notBool{}(brb{}(V:SortVal{})))",
            r"\top{R}()",
            "b-not"
        ),
        equation("t", "SortState{}", "failed{}()", r"\top{R}()", "t-failed"),
        equation(
            "t",
            "SortState{}",
            "flag{}(notBool{}(tb{}(V:SortVal{})))",
            r"\top{R}()",
            "t-not"
        ),
    ));
    let heads = definition.data_heads();
    // `t` guards the hooked rule apart from the argument rule: `tb(one)` is a stuck total
    // application, a defined argument, so only reading `notBool` as no value keeps it undecided.
    for label in ["s-failed", "b-failed", "t-failed"] {
        let finding = pair_finding(&heads, label);
        assert!(!finding.is_genuine(), "{label}: {:?}", finding.instance());
    }
}

/// S2B-T3: a total application one of whose equations matches with a `requires` the search does
/// not decide is not stuck, so it is no value: `p(V) = one` beside `p(V) = cap(V)` with
/// `cap(X0) = one requires und(V)`, `und` a partial function without an equation.
#[test]
fn a_total_application_with_an_undecided_equation_is_no_value() {
    let definition = with_sentences(&format!(
        "    symbol und{{}}(SortVal{{}}) : SortBool{{}} [function{{}}()]
    symbol cap{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]
    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}{}",
        equation(
            "cap",
            "SortVal{}",
            "one{}()",
            r#"\equals{SortBool{}, R}(und{}(V:SortVal{}), \dv{SortBool{}}("true"))"#,
            "cap-und"
        ),
        equation("p", "SortVal{}", "one{}()", r"\top{R}()", "p-one"),
        equation(
            "p",
            "SortVal{}",
            "cap{}(V:SortVal{})",
            r"\top{R}()",
            "p-cap"
        ),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "p-one");
    assert!(!finding.is_genuine(), "{:?}", finding.instance());
}

/// S2B-T3: a variable of a `Bytes` sort gets the candidates `""` and `"a"`, so `bf(B) = failed`
/// beside `bf(B) = bound(one)` is genuine at `bf("")`.
#[test]
fn a_bytes_variable_gets_candidates() {
    let definition = with_sentences(&format!(
        "    hooked-sort SortBytes{{}} [hook{{}}(\"BYTES.Bytes\"), hasDomainValues{{}}()]
    symbol bf{{}}(SortBytes{{}}) : SortState{{}} [function{{}}(), total{{}}()]
{}{}",
        r#"
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortBytes{}, R}(X0:SortBytes{}, B:SortBytes{}), \top{R}())),
        \equals{SortState{}, R}(bf{}(X0:SortBytes{}), \and{SortState{}}(failed{}(), \top{SortState{}}())))
        [label{}("bf-failed")]
"#,
        r#"
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortBytes{}, R}(X0:SortBytes{}, B:SortBytes{}), \top{R}())),
        \equals{SortState{}, R}(bf{}(X0:SortBytes{}), \and{SortState{}}(bound{}(one{}()), \top{SortState{}}())))
        [label{}("bf-bound")]
"#
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "bf-failed");
    let instance = finding.instance().expect("a genuine finding");
    assert_eq!(
        instance.overlap,
        term(&definition, r#"bf{}(\dv{SortBytes{}}(""))"#),
        "{instance:?}"
    );
}

/// Review S1: an axiom at a stuck total application's index that the evaluator does not apply
/// (`non-executable`, `symbolic`, `simplification`) still equates it with another term in every
/// model, so the application is no value: `p(V) = one` beside `p(V) = cap(V)` with `cap(X0) =
/// one` carrying each attribute stays undecided.
#[test]
fn a_total_application_an_unapplied_axiom_matches_is_no_value() {
    for attribute in ["non-executable{}()", "symbolic{}()"] {
        let definition = with_sentences(&format!(
            "{CAP}\n    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}{}",
            attributed_equation(
                "cap",
                "SortVal{}",
                "one{}()",
                r"\top{R}()",
                &format!(r#"label{{}}("cap-any"), {attribute}"#)
            ),
            equation("p", "SortVal{}", "one{}()", r"\top{R}()", "p-one"),
            equation(
                "p",
                "SortVal{}",
                "cap{}(V:SortVal{})",
                r"\top{R}()",
                "p-cap"
            ),
        ));
        let heads = definition.data_heads();
        let finding = pair_finding(&heads, "p-one");
        assert!(
            !finding.is_genuine(),
            "{attribute}: {:?}",
            finding.instance()
        );
    }
    let definition = with_sentences(&format!(
        r#"{CAP}
    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]
    axiom{{R}} \implies{{R}}(
        \top{{R}}(),
        \equals{{SortVal{{}}, R}}(cap{{}}(X:SortVal{{}}), \and{{SortVal{{}}}}(one{{}}(), \top{{SortVal{{}}}}())))
        [label{{}}("cap-lemma"), simplification{{}}()]
{}{}"#,
        equation("p", "SortVal{}", "one{}()", r"\top{R}()", "p-one"),
        equation(
            "p",
            "SortVal{}",
            "cap{}(V:SortVal{})",
            r"\top{R}()",
            "p-cap"
        ),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "p-one");
    assert!(
        !finding.is_genuine(),
        "simplification: {:?}",
        finding.instance()
    );
}

/// `cap2(listVal(Vs)) = one`, a second declared total function like [`CAP`].
const CAP2: &str = r#"
    symbol cap2{}(SortVal{}) : SortVal{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortVal{}, R}(X0:SortVal{}, listVal{}(Vs:SortVals{})), \top{R}())),
        \equals{SortVal{}, R}(cap2{}(X0:SortVal{}), \and{SortVal{}}(one{}(), \top{SortVal{}}())))
        [label{}("cap2-list")]
"#;

/// Review N1: an undefined value against a stuck total one is genuine: at `s(one)`,
/// `bound(nb(one))` is `\bottom` in `M_NF` and `bound(cap(one))` a normal form.
#[test]
fn an_undefined_value_against_a_stuck_total_value_is_genuine() {
    let definition = with_sentences(&format!(
        "{CAP}\n{NB}\n    symbol s{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation(
            "s",
            "SortState{}",
            "bound{}(nb{}(V:SortVal{}))",
            r"\top{R}()",
            "s-nb"
        ),
        equation(
            "s",
            "SortState{}",
            "bound{}(cap{}(V:SortVal{}))",
            r"\top{R}()",
            "s-cap"
        ),
    ));
    let heads = definition.data_heads();
    let instance = pair_finding(&heads, "s-nb")
        .instance()
        .expect("a genuine finding")
        .clone();
    assert_eq!(
        instance.overlap,
        term(&definition, "s{}(one{}())"),
        "{instance:?}"
    );
    let mut stuck = vec![instance.stuck.0, instance.stuck.1];
    stuck.sort();
    assert_eq!(
        stuck,
        [Some(Stuck::Total), Some(Stuck::Partial)],
        "{instance:?}"
    );
}

/// Review N1: two different stuck total values are two normal forms: at `p(one)`, `cap(one)`
/// and `cap2(one)`.
#[test]
fn two_different_stuck_total_values_are_genuine() {
    let definition = with_sentences(&format!(
        "{CAP}{CAP2}\n    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation(
            "p",
            "SortVal{}",
            "cap{}(V:SortVal{})",
            r"\top{R}()",
            "p-cap"
        ),
        equation(
            "p",
            "SortVal{}",
            "cap2{}(V:SortVal{})",
            r"\top{R}()",
            "p-cap2"
        ),
    ));
    let heads = definition.data_heads();
    let instance = pair_finding(&heads, "p-cap")
        .instance()
        .expect("a genuine finding")
        .clone();
    assert_eq!(
        instance.overlap,
        term(&definition, "p{}(one{}())"),
        "{instance:?}"
    );
    assert_eq!(
        instance.stuck,
        (Some(Stuck::Total), Some(Stuck::Total)),
        "{instance:?}"
    );
}

/// Review N1: an undefined item makes its collection undefined: `l(V) = .List` beside `l(V) =
/// ListItem(nb(V))` is genuine at `l(one)`, the second value `partial`.
#[test]
fn an_undefined_list_item_is_an_undefined_value() {
    let definition = with_sentences(&format!(
        r#"{NB}
    hooked-sort SortList{{}}
        [hook{{}}("LIST.List"), unit{{}}(Lbl'Stop'List{{}}()), element{{}}(LblListItem{{}}()),
         concat{{}}(Lbl'Unds'List'Unds'{{}}())]
    hooked-symbol Lbl'Stop'List{{}}() : SortList{{}} [function{{}}(), total{{}}(), hook{{}}("LIST.unit")]
    hooked-symbol LblListItem{{}}(SortVal{{}}) : SortList{{}}
        [function{{}}(), total{{}}(), hook{{}}("LIST.element")]
    hooked-symbol Lbl'Unds'List'Unds'{{}}(SortList{{}}, SortList{{}}) : SortList{{}}
        [function{{}}(), total{{}}(), hook{{}}("LIST.concat"), assoc{{}}()]
    symbol l{{}}(SortVal{{}}) : SortList{{}} [function{{}}(), total{{}}()]
{}{}"#,
        equation(
            "l",
            "SortList{}",
            "Lbl'Stop'List{}()",
            r"\top{R}()",
            "l-empty"
        ),
        equation(
            "l",
            "SortList{}",
            "LblListItem{}(nb{}(V:SortVal{}))",
            r"\top{R}()",
            "l-item"
        ),
    ));
    let heads = definition.data_heads();
    let instance = pair_finding(&heads, "l-empty")
        .instance()
        .expect("a genuine finding")
        .clone();
    assert_eq!(
        instance.overlap,
        term(&definition, "l{}(one{}())"),
        "{instance:?}"
    );
    let mut stuck = vec![instance.stuck.0, instance.stuck.1];
    stuck.sort();
    assert_eq!(stuck, [None, Some(Stuck::Partial)], "{instance:?}");
}

/// Review N1: a stuck application of a `functional` symbol that is no declared function is no
/// value (an uninterpreted symbol, which no `M_NF` normal-form claim covers): `p(V) = one`
/// beside `p(V) = q(V)` stays undecided.
#[test]
fn a_functional_uninterpreted_application_is_no_value() {
    let definition = with_sentences(&format!(
        "    symbol q{{}}(SortVal{{}}) : SortVal{{}} [functional{{}}()]
    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation("p", "SortVal{}", "one{}()", r"\top{R}()", "p-one"),
        equation("p", "SortVal{}", "q{}(V:SortVal{})", r"\top{R}()", "p-q"),
    ));
    let heads = definition.data_heads();
    let finding = pair_finding(&heads, "p-one");
    assert!(!finding.is_genuine(), "{:?}", finding.instance());
}
