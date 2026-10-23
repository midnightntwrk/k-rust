//! Data terms (`k_rust_backend::data_term`): which ground terms are data, and which overload
//! heads two definitions agree on. The fixture is FUN's overloaded list family
//! (`tests/fixtures/overloaded-list-owise.kore`): `exps`, `vals` and `listExp` root only overload
//! equations, `pipe` is an `anywhere` head with no equation, `ordinaryVals` a declared function.

use k_rust_backend::{data_term::DataHeads, definition::BackendDefinition, term::Term};
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
    // The finding is genuine (FZ-POLISH): at `q(one)` the two equations give `one` and
    // `inj(bottom)`, two different constructor terms.
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
    let assumed = definition.data_heads_assuming(&heads, |finding| finding.is_genuine());
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
