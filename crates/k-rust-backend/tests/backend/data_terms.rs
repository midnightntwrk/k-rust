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
    // The tainted family's overload equations mention the constructors they lower to; the
    // family may identify those too (FZ-DATAEND review B2), so no term holding one is data,
    // constructor-like or not.
    let refused: Vec<String> = heads.refused().map(ToString::to_string).collect();
    for symbol in ["bottoms", "dotBottoms", "vals", "exps"] {
        assert!(refused.iter().any(|name| name == symbol), "{refused:?}");
    }
    assert!(!data(&definition, &heads, EMPTY_EXPS));
    assert!(data(&definition, &heads, "fun{}()"));
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
    // then outside the check's premises, so no member of the family, and nothing its overload
    // equations lower to, is data.
    assert!(
        definition
            .value_claims()
            .violations()
            .iter()
            .any(|violation| !violation.kind.withdraws())
    );
    assert!(heads.refused().any(|name| name.as_ref() == "vals"));
    assert!(!data(
        &definition,
        &heads,
        &format!("vals{{}}(one{{}}(), {EMPTY_VALS})")
    ));
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

#[test]
fn two_definitions_agree_on_the_heads_whose_overload_equations_are_equal() {
    let baseline = definition(FIXTURE);
    let same = definition(FIXTURE);
    assert_eq!(
        baseline.data_heads().agreeing_with(&same.data_heads()),
        baseline.data_heads()
    );
    // Without its overload equation `listExp` roots no equation, and its applications denote
    // other values: `[one]` is `inj(listVal(one))` in the baseline and itself there.
    let unlowered = without_sentence("symbol-overload{}(listExp{}(), listVal{}())");
    assert_eq!(
        names(&baseline.data_heads().agreeing_with(&unlowered.data_heads())),
        ["dotExps", "dotVals", "exps", "vals"]
    );
}

/// Whether an overload equation applies reads the subsort order below the sorts its arguments
/// inject from. A new sort below `Val` changes what `exps(inj{Val,Exp}(K0), ..)` matches, so
/// `exps` no longer means the same in both definitions; `vals` and `listExp`, whose equations
/// read only `Bottom` and `Vals`, still do.
#[test]
fn two_definitions_disagree_on_a_head_whose_argument_sorts_have_other_subsorts() {
    let baseline = definition(FIXTURE);
    let mutant = with_sentences(
        r#"
    sort SortZero{} []
    symbol zero{}() : SortZero{} [constructor{}()]
    axiom{R} \exists{R}(V:SortVal{}, \equals{SortVal{}, R}(V:SortVal{}, inj{SortZero{}, SortVal{}}(F:SortZero{})))
        [subsort{SortZero{}, SortVal{}}()]
    axiom{R} \exists{R}(V:SortExp{}, \equals{SortExp{}, R}(V:SortExp{}, inj{SortZero{}, SortExp{}}(F:SortZero{})))
        [subsort{SortZero{}, SortExp{}}()]
"#,
    );
    let agreeing = baseline.data_heads().agreeing_with(&mutant.data_heads());
    assert_eq!(names(&agreeing), ["dotExps", "dotVals", "listExp", "vals"]);
    let zero = format!("exps{{}}(inj{{SortZero{{}}, SortExp{{}}}}(zero{{}}()), {EMPTY_EXPS})");
    assert!(!mutant.is_data(&term(&mutant, &zero), &mutant.data_heads()));
    assert!(mutant.is_data(&term(&mutant, FUN_EXPS), &mutant.data_heads()));
    assert!(!mutant.is_data(&term(&mutant, FUN_EXPS), &agreeing));
    assert!(mutant.is_data(
        &term(&mutant, &format!("vals{{}}(one{{}}(), {EMPTY_VALS})")),
        &agreeing
    ));
}
