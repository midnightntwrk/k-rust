//! Values the definition leaves to the implementation are computed only inside an execution.
//!
//! `keys_list`, `values` and `Set2List` of two or more items list them in an order domains.md does
//! not fix. Outside an execution (`EvaluationMode::Proof`, the mode when no execution or search is
//! running) such an application stays unevaluated, as a defined value; inside one it is the
//! listing in k-rust's order. With zero or one item every listing is the same, so it is evaluated
//! in every mode.

use k_rust_backend::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    evaluation::{EvaluationMode, current, with_evaluation},
    rewrite::{ExecutionOptions, Pattern, execute_with_solver_and_observer},
    rule::Predicate,
    search::{SearchOptions, SearchType, search_graph_with_solver_and_observer},
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::{Term, TermKind},
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped};

const FIXTURE: &str = r#"[]
module MAIN
  sort SortK{} []
  sort SortKItem{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  sort SortString{} [hasDomainValues{}()]
  symbol inj{From, To}(From) : To [sortInjection{}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
      [subsort{SortInt{}, SortKItem{}}()]

  hooked-sort SortList{}
    [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
     concat{}(Lbl'Unds'List'Unds'{}())]
  hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]

  hooked-sort SortSet{}
    [hook{}("SET.Set"), unit{}(Lbl'Stop'Set{}()), element{}(LblSetItem{}()),
     concat{}(Lbl'Unds'Set'Unds'{}())]
  hooked-symbol Lbl'Stop'Set{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol LblSetItem{}(SortKItem{}) : SortSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol Lbl'Unds'Set'Unds'{}(SortSet{}, SortSet{}) : SortSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

  hooked-sort SortMap{}
    [hook{}("MAP.Map"), unit{}(Lbl'Stop'Map{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
     concat{}(Lbl'Unds'Map'Unds'{}())]
  hooked-symbol Lbl'Stop'Map{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

  hooked-symbol keysList{}(SortMap{}) : SortList{} [function{}(), hook{}("MAP.keys_list")]
  hooked-symbol values{}(SortMap{}) : SortList{} [function{}(), hook{}("MAP.values")]
  hooked-symbol setToList{}(SortSet{}) : SortList{}
    [function{}(), total{}(), hook{}("SET.set2list")]

  symbol dotk{}() : SortK{} [constructor{}()]
  hooked-symbol log{}(SortString{}) : SortK{} [function{}(), total{}(), hook{}("IO.logString")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("evaluation mode fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("evaluation mode fixture should internalize")
}

fn int(value: i64) -> String {
    format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
}

/// The map binding each key to `key + 100`.
fn map(keys: &[i64]) -> String {
    keys.iter()
        .map(|key| {
            format!(
                "Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {})",
                int(*key),
                int(key + 100)
            )
        })
        .reduce(|left, right| format!("Lbl'Unds'Map'Unds'{{}}({left}, {right})"))
        .unwrap_or_else(|| "Lbl'Stop'Map{}()".into())
}

fn set(elements: &[i64]) -> String {
    elements
        .iter()
        .map(|element| format!("LblSetItem{{}}({})", int(*element)))
        .reduce(|left, right| format!("Lbl'Unds'Set'Unds'{{}}({left}, {right})"))
        .unwrap_or_else(|| "Lbl'Stop'Set{}()".into())
}

/// Every listing application of the test: `keys_list`, `values` and `Set2List` over `items`.
fn listings(items: &[i64]) -> [String; 3] {
    [
        format!("keysList{{}}({})", map(items)),
        format!("values{{}}({})", map(items)),
        format!("setToList{{}}({})", set(items)),
    ]
}

/// The simplification of `source`, and the diagnostics it emitted.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<BackendDiagnostic>) {
    let term = internal_term(definition, source);
    let (result, diagnostics) = diagnostic::collect(|| {
        unstopped::simplify(definition, &term, SimplificationOptions::default())
    });
    (
        result.expect("a listing simplifies without an error").term,
        diagnostics,
    )
}

fn is_list(term: &Term) -> bool {
    matches!(term.kind(), TermKind::List { rest: None, .. })
}

/// Outside an execution, a listing of two or more items stays unevaluated, without the
/// unsupported-hook warning (the outcome is the documented one), while a listing of zero or one
/// item, which every order gives alike, is evaluated.
#[test]
fn a_listing_of_two_or_more_items_stays_unevaluated_outside_an_execution() {
    let definition = definition();
    assert_eq!(current(), EvaluationMode::Proof);
    for source in listings(&[10, 2, -1]) {
        let (term, diagnostics) = simplified(&definition, &source);
        assert_eq!(
            term,
            internal_term(&definition, &source),
            "{source}: {term:?}"
        );
        assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
    }
    for items in [&[][..], &[7][..]] {
        for source in listings(items) {
            let (term, _) = simplified(&definition, &source);
            assert!(is_list(&term), "{source}: {term:?}");
        }
    }
}

/// Inside an execution every listing is evaluated, in k-rust's order: decimal text order for Int
/// keys.
#[test]
fn a_listing_is_evaluated_inside_an_execution() {
    let definition = definition();
    for source in listings(&[10, 2, -1]) {
        let (term, _) = with_evaluation(EvaluationMode::Execution, || {
            simplified(&definition, &source)
        });
        assert!(is_list(&term), "{source}: {term:?}");
    }
    let (keys, _) = with_evaluation(EvaluationMode::Execution, || {
        simplified(&definition, &listings(&[10, 2, -1])[0])
    });
    let expected = internal_term(
        &definition,
        &format!(
            "Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({}), Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({}), LblListItem{{}}({})))",
            int(-1),
            int(10),
            int(2)
        ),
    );
    assert_eq!(keys, expected);
}

/// A listing left unevaluated is a defined value: a closed map with distinct constructor-like
/// keys has a listing, so the `\ceil` of the partial `keys_list` and `values` holds.
#[test]
fn an_unevaluated_listing_is_defined() {
    let definition = definition();
    for source in listings(&[10, 2, -1]) {
        let predicate = Predicate::Ceil(internal_term(&definition, &source));
        let simplified = unstopped::simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("the definedness of a listing simplifies");
        assert_eq!(simplified, Predicate::True, "{source}");
    }
}

/// A request that does not say it runs a program evaluates only consequences of the definition.
#[test]
fn execution_and_search_options_default_to_proof() {
    assert_eq!(
        ExecutionOptions::default().evaluation,
        EvaluationMode::Proof
    );
    assert_eq!(SearchOptions::default().evaluation, EvaluationMode::Proof);
}

/// An effect observer is the caller's code, not part of the run: whatever it evaluates while an
/// execution or a search in `Execution` mode reports an effect is outside the execution, so a
/// listing of two or more items stays unevaluated there.
#[test]
fn an_effect_observer_evaluates_outside_the_execution() {
    let definition = definition();
    let listing = internal_term(&definition, &listings(&[10, 2, -1])[0]);
    let initial = Pattern {
        term: internal_term(&definition, r#"log{}(\dv{SortString{}}("effect"))"#),
        constraints: Vec::new(),
    };
    let observe = |modes: &mut Vec<(EvaluationMode, bool)>, effect: &BuiltinEffect| {
        assert_eq!(*effect, BuiltinEffect::UserLog("effect".into()));
        let evaluated =
            unstopped::simplify(&definition, &listing, SimplificationOptions::default())
                .expect("a listing simplifies")
                .term;
        modes.push((current(), is_list(&evaluated)));
    };

    let mut executed = Vec::new();
    let result = execute_with_solver_and_observer(
        &definition,
        initial.clone(),
        ExecutionOptions {
            evaluation: EvaluationMode::Execution,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |effect| observe(&mut executed, effect),
    );
    assert_eq!(result.effects.len(), 1, "{result:?}");
    assert_eq!(executed, [(EvaluationMode::Proof, false)]);

    let mut searched = Vec::new();
    search_graph_with_solver_and_observer(
        &definition,
        initial,
        SearchOptions {
            search_type: SearchType::Star,
            evaluation: EvaluationMode::Execution,
            ..SearchOptions::default()
        },
        &NoSolver,
        |effect| observe(&mut searched, effect),
    );
    assert!(!searched.is_empty());
    assert!(
        searched
            .iter()
            .all(|observed| *observed == (EvaluationMode::Proof, false)),
        "{searched:?}"
    );
    assert_eq!(current(), EvaluationMode::Proof);
}

/// A listing over a map whose keys are constructor-like and whose values are symbolic stays
/// unevaluated outside an execution too, and is defined exactly when the map is: with element
/// variables as values, the map, and so the listing, is defined.
#[test]
fn a_listing_of_a_map_with_symbolic_values_is_as_defined_as_the_map() {
    let definition = definition();
    let map = format!(
        "Lbl'Unds'Map'Unds'{{}}(Lbl'UndsPipe'-'-GT-Unds'{{}}({}, X:SortKItem{{}}), Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {}))",
        int(1),
        int(2),
        int(3)
    );
    for source in [format!("keysList{{}}({map})"), format!("values{{}}({map})")] {
        let (term, _) = simplified(&definition, &source);
        assert_eq!(term, internal_term(&definition, &source), "{source}");
        let simplified = unstopped::simplify_predicate_with_solver(
            &definition,
            &Predicate::Ceil(term),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("the definedness of a listing simplifies");
        assert_eq!(simplified, Predicate::True, "{source}");
    }
}

/// GAP K1: hooks whose outcome the declaring text leaves open, at partial and `total` symbols.
const OPEN_OUTCOMES: &str = r#"[]
module MAIN
  sort SortK{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
  hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
  sort SortG1Point{} []
  symbol g1{}(SortInt{}, SortInt{}) : SortG1Point{} [constructor{}()]
  hooked-symbol add{}(SortG1Point{}, SortG1Point{}) : SortG1Point{}
    [function{}(), hook{}("KRYPTO.bn128add")]
  hooked-symbol totalAdd{}(SortG1Point{}, SortG1Point{}) : SortG1Point{}
    [function{}(), total{}(), hook{}("KRYPTO.bn128add")]
  hooked-symbol rec{}(SortBytes{}, SortInt{}, SortBytes{}, SortBytes{}) : SortBytes{}
    [function{}(), hook{}("KRYPTO.ecdsaRecover")]
  hooked-symbol totalRec{}(SortBytes{}, SortInt{}, SortBytes{}, SortBytes{}) : SortBytes{}
    [function{}(), total{}(), hook{}("KRYPTO.ecdsaRecover")]
  hooked-symbol s2b{}(SortString{}) : SortBytes{}
    [function{}(), total{}(), hook{}("BYTES.string2bytes")]
endmodule []"#;

/// The `\ceil` of `source` simplified in `mode`.
fn definedness(definition: &BackendDefinition, source: &str, mode: EvaluationMode) -> Predicate {
    let predicate = Predicate::Ceil(internal_term(definition, source));
    with_evaluation(mode, || {
        unstopped::simplify_predicate_with_solver(
            definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("the definedness simplifies")
    })
}

/// GAP K1: outside an execution a value of class `outside-domain` at a partial symbol is of
/// unknown definedness, since `\bottom` is a model too: the `\ceil` of a BN128 sum of a
/// non-point (k-rust's pick is `\bottom`) and of a failed recovery (k-rust's pick is the empty
/// `Bytes`) is neither true nor false. At a `total` symbol, and for a hook whose value is
/// determined (`String2Bytes`, AM-1), the application is defined. An execution takes k-rust's
/// pick. Before K1 the proof routes read the pick: the sum was undefined and the recovery
/// defined.
#[test]
fn an_open_outcome_of_a_partial_symbol_is_of_unknown_definedness_outside_an_execution() {
    let syntax = parse_definition(OPEN_OUTCOMES).expect("the fixture parses");
    let definition = BackendDefinition::internalize(&syntax, "MAIN").expect("it internalizes");
    let int = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
    let sum = format!(
        "add{{}}(g1{{}}({}, {}), g1{{}}({}, {}))",
        int(0),
        int(0),
        int(1),
        int(3)
    );
    let empty = r#"\dv{SortBytes{}}("")"#;
    let failed = |symbol: &str| format!("{symbol}{{}}({empty}, {}, {empty}, {empty})", int(29));
    for source in [sum.as_str(), failed("rec").as_str()] {
        let proof = definedness(&definition, source, EvaluationMode::Proof);
        assert!(
            !matches!(proof, Predicate::True | Predicate::False),
            "{source}: {proof:?}"
        );
    }
    for source in [
        failed("totalRec"),
        r#"s2b{}(\dv{SortString{}}("a"))"#.to_owned(),
    ] {
        assert_eq!(
            definedness(&definition, &source, EvaluationMode::Proof),
            Predicate::True,
            "{source}"
        );
    }
    // A `total` BN128 sum of a non-point is defined in every model, and no text gives its value:
    // no route takes k-rust's `\bottom` (GAP K2 fix round 1).
    let total_sum = sum.replacen("add{}", "totalAdd{}", 1);
    for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
        assert_eq!(
            definedness(&definition, &total_sum, mode),
            Predicate::True,
            "{mode:?}"
        );
    }
    assert_eq!(
        definedness(&definition, &sum, EvaluationMode::Execution),
        Predicate::False
    );
    assert_eq!(
        definedness(&definition, &failed("rec"), EvaluationMode::Execution),
        Predicate::True
    );
}

/// GAP A1: hooks whose values the amendments AM-1, AM-2, AM-3 and AM-7 of `docs/amendments.md`
/// determine.
const AMENDED: &str = r#"[]
module MAIN
  sort SortK{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
  hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
  sort SortG1Point{} []
  symbol g1{}(SortInt{}, SortInt{}) : SortG1Point{} [constructor{}()]
  hooked-symbol add{}(SortG1Point{}, SortG1Point{}) : SortG1Point{}
    [function{}(), hook{}("KRYPTO.bn128add")]
  hooked-symbol valid{}(SortG1Point{}) : SortBool{} [function{}(), hook{}("KRYPTO.bn128valid")]
  hooked-symbol keccak{}(SortBytes{}) : SortString{} [function{}(), hook{}("KRYPTO.keccak256")]
  hooked-symbol s2b{}(SortString{}) : SortBytes{}
    [function{}(), total{}(), hook{}("BYTES.string2bytes")]
  hooked-symbol b2s{}(SortBytes{}) : SortString{}
    [function{}(), total{}(), hook{}("BYTES.bytes2string")]
  hooked-symbol rep{}(SortBytes{}, SortInt{}, SortBytes{}) : SortBytes{}
    [function{}(), hook{}("BYTES.replaceAt")]
endmodule []"#;

/// GAP A1: a value an amendment determines is evaluated outside an execution, as in one, without
/// a warning: `String2Bytes` and `Bytes2String` one byte per code point (AM-1), a hex digest in
/// lowercase (AM-2), a BN128 sum of points and the validity of a pair (AM-3), and a replacement up
/// to the end of the `Bytes` (AM-7). Before A1 each stayed unevaluated outside an execution.
#[test]
fn an_amended_value_is_evaluated_outside_an_execution() {
    let syntax = parse_definition(AMENDED).expect("the fixture parses");
    let definition = BackendDefinition::internalize(&syntax, "MAIN").expect("it internalizes");
    let int = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
    let point = |x: i64, y: i64| format!("g1{{}}({}, {})", int(x), int(y));
    let cases = [
        (
            r#"s2b{}(\dv{SortString{}}("a\xe9\xff"))"#.to_owned(),
            r#"\dv{SortBytes{}}("a\xe9\xff")"#.to_owned(),
        ),
        (
            r#"b2s{}(\dv{SortBytes{}}("a\xe9\xff"))"#.to_owned(),
            r#"\dv{SortString{}}("a\xe9\xff")"#.to_owned(),
        ),
        (
            r#"keccak{}(\dv{SortBytes{}}(""))"#.to_owned(),
            r#"\dv{SortString{}}("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")"#
                .to_owned(),
        ),
        (
            format!("add{{}}({}, {})", point(0, 0), point(1, 2)),
            point(1, 2),
        ),
        (
            format!("valid{{}}({})", point(1, 2)),
            r#"\dv{SortBool{}}("true")"#.to_owned(),
        ),
        (
            format!("valid{{}}({})", point(1, 3)),
            r#"\dv{SortBool{}}("false")"#.to_owned(),
        ),
        (
            format!(
                r#"rep{{}}(\dv{{SortBytes{{}}}}("\x01\x02\x03"), {}, \dv{{SortBytes{{}}}}("\x00\x00"))"#,
                int(1)
            ),
            r#"\dv{SortBytes{}}("\x01\x00\x00")"#.to_owned(),
        ),
    ];
    for (source, expected) in &cases {
        let expected = internal_term(&definition, expected);
        for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
            let (term, diagnostics) = with_evaluation(mode, || simplified(&definition, source));
            assert_eq!(term, expected, "{source} {mode:?}");
            assert!(diagnostics.is_empty(), "{source} {mode:?}: {diagnostics:?}");
        }
    }
}

/// GAP K2: partial and `total` symbols hooked at scoped sites (`ordChar`, `String2Int`) and at a
/// universal one (`chrChar`).
const OUTSIDE_BOTTOMS: &str = r#"[]
module MAIN
  sort SortK{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
  hooked-symbol ord{}(SortString{}) : SortInt{} [function{}(), hook{}("STRING.ord")]
  hooked-symbol totalOrd{}(SortString{}) : SortInt{}
    [function{}(), total{}(), hook{}("STRING.ord")]
  hooked-symbol s2i{}(SortString{}) : SortInt{} [function{}(), hook{}("STRING.string2int")]
  hooked-symbol chr{}(SortInt{}) : SortString{} [function{}(), hook{}("STRING.chr")]
  hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
  hooked-symbol rep{}(SortBytes{}, SortInt{}, SortBytes{}) : SortBytes{}
    [function{}(), hook{}("BYTES.replaceAt")]
endmodule []"#;

/// GAP K2: where a partial hook's description covers only some arguments, `\bottom` and every
/// value are models outside them, so the `\ceil` of `ordChar("ab")` and `String2Int("x")` is
/// neither true nor false outside an execution, and false in one, which takes k-rust's
/// `\bottom`. At a `total` symbol the application is defined on every route: `\bottom` is no
/// model there. `chrChar(-1)` is `\bottom` in every model (no character has that number), on
/// every route. Before K2 every route took the `\bottom`.
#[test]
fn a_bottom_outside_a_described_domain_is_of_unknown_definedness_outside_an_execution() {
    let syntax = parse_definition(OUTSIDE_BOTTOMS).expect("the fixture parses");
    let definition = BackendDefinition::internalize(&syntax, "MAIN").expect("it internalizes");
    let string = |value: &str| format!(r#"\dv{{SortString{{}}}}("{value}")"#);
    let rep = |index: i64| {
        format!(
            r#"rep{{}}(\dv{{SortBytes{{}}}}("\x01\x02\x03"), \dv{{SortInt{{}}}}("{index}"), \dv{{SortBytes{{}}}}("\x00\x00"))"#
        )
    };
    // `replaceAtBytes` at a negative index (`index + N` an index) is of unknown definedness
    // outside an execution, which takes k-rust's `\bottom`; where `index + N` is the length it is
    // defined, the replaced `Bytes` (AM-7), on every route.
    for (index, defined) in [
        (0, Predicate::True),
        (1, Predicate::True),
        (2, Predicate::False),
        (-3, Predicate::False),
    ] {
        for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
            assert_eq!(
                definedness(&definition, &rep(index), mode),
                defined,
                "{index} {mode:?}"
            );
        }
    }
    let scoped = [
        format!("ord{{}}({})", string("ab")),
        format!("s2i{{}}({})", string("x")),
        rep(-1),
    ];
    for source in &scoped {
        let proof = definedness(&definition, source, EvaluationMode::Proof);
        assert!(
            !matches!(proof, Predicate::True | Predicate::False),
            "{source}: {proof:?}"
        );
        assert_eq!(
            definedness(&definition, source, EvaluationMode::Execution),
            Predicate::False,
            "{source}"
        );
    }
    let total = format!("totalOrd{{}}({})", string("ab"));
    let universal = r#"chr{}(\dv{SortInt{}}("-1"))"#;
    for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
        assert_eq!(
            definedness(&definition, &total, mode),
            Predicate::True,
            "{mode:?}"
        );
        assert_eq!(
            definedness(&definition, universal, mode),
            Predicate::False,
            "{mode:?}"
        );
        assert_eq!(
            definedness(&definition, &format!("ord{{}}({})", string("a")), mode),
            Predicate::True,
            "{mode:?}"
        );
    }
}
